{-# LANGUAGE PatternSynonyms #-}

module Main where

import qualified Data.Map.Strict as Map
  ( Map,
    empty,
    foldMapWithKey,
    insert,
    lookup,
  )
import Data.Maybe (fromMaybe)
import Data.Text.Lazy (unpack)
import ShellCheck.AST
  ( AssignmentMode (..),
    CaseType (..),
    Id,
    InnerToken (..),
    Token (..),
    getId,
    pattern T_Annotation,
    pattern T_Assignment,
    pattern T_CaseExpression,
    pattern T_DollarBraced,
    pattern T_DoubleQuoted,
    pattern T_Glob,
    pattern T_Literal,
    pattern T_NormalWord,
    pattern T_Pipeline,
    pattern T_Redirecting,
    pattern T_Script,
    pattern T_SimpleCommand,
    pattern T_SingleQuoted,
  )
import ShellCheck.Interface
  ( ParseResult (..),
    ParseSpec (..),
    SystemInterface (..),
    newParseSpec,
  )
import ShellCheck.Parser (parseScript)
import Text.Pretty.Simple (pPrint, pShowNoColor)

sys :: SystemInterface IO
sys =
  SystemInterface
    { siReadFile = const (return (Left "Not implemented")),
      siFindSource = \_ _ sourcedFile -> return sourcedFile,
      siGetConfig = const (return Nothing)
    }

data Value
  = Lit String
  | Var String
  | Glob String
  | Concat [Value]
  | Matches Value Value
  | Not Value
  | Any Token
  deriving (Show)

newtype LocBase t
  = Block [t]
  deriving (Show)

instance Functor LocBase where
  fmap f (Block ts) = Block (fmap f ts)

type Loc = LocBase Token

data StateBase t = State
  { stStack :: [LocBase t],
    stVars :: Map.Map String Value,
    stConstraints :: [Value]
  }
  deriving (Show)

instance Functor StateBase where
  fmap f state =
    State
      { stStack = map (fmap f) (stStack state),
        stVars = stVars state,
        stConstraints = stConstraints state
      }

type State = StateBase Token

initialState :: Token -> State
initialState entry =
  State
    { stStack = [Block [entry]],
      stVars = Map.empty,
      stConstraints = []
    }

data ExplorationStateBase t = ExplorationState
  { exActive :: [StateBase t],
    exDone :: [StateBase t],
    exFailed :: [StateBase t]
  }
  deriving (Show)

instance Functor ExplorationStateBase where
  fmap f explorationState =
    ExplorationState
      { exActive = map (fmap f) (exActive explorationState),
        exDone = map (fmap f) (exDone explorationState),
        exFailed = map (fmap f) (exFailed explorationState)
      }

type ExplorationState = ExplorationStateBase Token

newExplorationState :: ExplorationState
newExplorationState =
  ExplorationState
    { exActive = [],
      exDone = [],
      exFailed = []
    }

addActive :: State -> ExplorationState -> ExplorationState
addActive state explorationState =
  explorationState
    { exActive = state : exActive explorationState
    }

addDone :: State -> ExplorationState -> ExplorationState
addDone state explorationState =
  explorationState
    { exDone = state : exDone explorationState
    }

pushLoc :: Loc -> State -> State
pushLoc loc state = state {stStack = loc : stStack state}

mergeExplorationStates ::
  ExplorationState ->
  ExplorationState ->
  ExplorationState
mergeExplorationStates state1 state2 =
  ExplorationState
    { exActive = exActive state1 ++ exActive state2,
      exDone = exDone state1 ++ exDone state2,
      exFailed = exFailed state1 ++ exFailed state2
    }

evalVar :: String -> State -> Value
evalVar var state = case Map.lookup var (stVars state) of
  Just val -> val
  Nothing -> Var var

concat' :: [Value] -> Value
concat' [t0] = t0
concat' ts = Concat ts

eval :: Token -> State -> Value
eval token state = case token of
  T_Literal _ val -> Lit val
  T_SingleQuoted _ val -> Lit val
  T_Glob _ val -> Glob val
  T_NormalWord _ parts -> concat' (map (`eval` state) parts)
  T_DoubleQuoted
    _
    [ T_DollarBraced _ False (T_NormalWord _ [T_Literal _ var])
      ] -> evalVar var state
  T_DollarBraced _ True (T_NormalWord _ [T_Literal _ var]) -> evalVar var state
  _ -> Any token

assign :: String -> Token -> State -> State
assign var token state =
  let val = eval token state
   in state {stVars = Map.insert var val (stVars state)}

forkCase ::
  Value ->
  [(CaseType, [Token], [Token])] ->
  [Value] ->
  State ->
  ExplorationState ->
  ExplorationState
forkCase word branches constraints state explorationState = case branches of
  (CaseBreak, pattern' : otherPatterns, tokens) : otherBranches ->
    let matches = Matches word (eval pattern' state)
        branchState =
          ( (pushLoc (Block tokens) state)
              { stConstraints = matches : constraints
              }
          )
     in forkCase
          word
          ((CaseBreak, otherPatterns, tokens) : otherBranches)
          (Not matches : constraints)
          state
          (addActive branchState explorationState)
  (CaseBreak, [], _) : otherBranches ->
    forkCase
      word
      otherBranches
      constraints
      state
      explorationState
  [] -> addActive (state {stConstraints = constraints}) explorationState
  incomplete -> error (unpack (pShowNoColor incomplete))

stepWith :: Token -> State -> ExplorationState
stepWith currentToken state =
  let single :: State -> ExplorationState
      single updatedState = newExplorationState {exActive = [updatedState]}
   in case currentToken of
        T_Annotation _ _ t -> single (pushLoc (Block [t]) state)
        T_Script _ _ ts -> single (pushLoc (Block ts) state)
        T_Pipeline _ [] [t] -> single (pushLoc (Block [t]) state)
        T_Redirecting _ [] t -> single (pushLoc (Block [t]) state)
        T_SimpleCommand _ [T_Assignment _ Assign var [] t] [] ->
          single (assign var t state)
        T_CaseExpression _ word branches ->
          forkCase
            (eval word state)
            branches
            (stConstraints state)
            state
            newExplorationState
        _ ->
          newExplorationState
            { exFailed = [pushLoc (Block [currentToken]) state]
            }

step :: State -> ExplorationState
step state =
  case stStack state of
    (Block (t : ts) : rest) -> stepWith t (state {stStack = Block ts : rest})
    ((Block []) : rest) -> step (state {stStack = rest})
    [] -> newExplorationState {exDone = [state]}

exploreOnce :: ExplorationState -> ExplorationState
exploreOnce state =
  let nextStates = map step (exActive state)
   in foldl mergeExplorationStates (state {exActive = []}) nextStates

explore :: ExplorationState -> ExplorationState
explore state =
  if null (exActive state) then state else explore (exploreOnce state)

main :: IO ()
main = do
  contents <- readFile "gcc/config.gcc"
  parseResult <- parseScript sys newParseSpec {psScript = contents}
  case prRoot parseResult of
    Just root ->
      let state =
            explore (newExplorationState {exActive = [initialState root]})
          dump = fmap getId state
       in do
            putStrLn "Root:"
            pPrint root
            putStrLn "Active:"
            mapM_ pPrint (exActive dump)
            putStrLn "Done:"
            mapM_ pPrint (exDone dump)
            putStrLn "Failed:"
            mapM_ pPrint (exFailed dump)
    Nothing -> putStrLn "Couldn't parse"

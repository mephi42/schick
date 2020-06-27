{-# LANGUAGE PatternSynonyms #-}

module Main where

import Data.Bifunctor (bimap)
import qualified Data.Map.Strict as Map
  ( Map,
    empty,
    insert,
    lookup,
  )
import Data.Text.Lazy (unpack)
import Options.Applicative
  ( Parser,
    argument,
    auto,
    execParser,
    fullDesc,
    helper,
    info,
    long,
    metavar,
    option,
    optional,
    str,
    (<**>),
  )
import ShellCheck.AST
  ( AssignmentMode (..),
    CaseType (..),
    Token (..),
    getId,
    pattern T_Annotation,
    pattern T_Assignment,
    pattern T_CaseExpression,
    pattern T_DollarBraced,
    pattern T_DoubleQuoted,
    pattern T_Glob,
    pattern T_IfExpression,
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
  | Eq Value Value
  | Any Token
  deriving (Show)

data LocBase t
  = Block [t]
  | If [t] [([t], [t])] [t]
  deriving (Show)

instance Functor LocBase where
  fmap f (Block ts) = Block (fmap f ts)
  fmap f (If thenBranch elifBranches elseBranch) =
    If
      (fmap f thenBranch)
      (map (bimap (fmap f) (fmap f)) elifBranches)
      (fmap f elseBranch)

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
  fmap f state =
    ExplorationState
      { exActive = map (fmap f) (exActive state),
        exDone = map (fmap f) (exDone state),
        exFailed = map (fmap f) (exFailed state)
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
        T_Annotation _ _ t -> stepWith t state
        T_Script _ _ ts -> single (pushLoc (Block ts) state)
        T_Pipeline _ [] [t] -> stepWith t state
        T_Redirecting _ [] t -> stepWith t state
        T_SimpleCommand _ [T_Assignment _ Assign var [] t] [] ->
          single (assign var t state)
        -- TODO: store command
        -- TODO: update $?
        -- TODO: check for exit
        T_SimpleCommand _ [] _ -> single state
        T_CaseExpression _ word branches ->
          forkCase
            (eval word state)
            branches
            (stConstraints state)
            state
            newExplorationState
        T_IfExpression _ ((c, t) : elifBranches) elseBranch ->
          let state' = pushLoc (If t elifBranches elseBranch) state
           in single (pushLoc (Block c) state')
        _ ->
          newExplorationState
            { exFailed = [pushLoc (Block [currentToken]) state]
            }

step :: State -> ExplorationState
step state =
  case stStack state of
    Block (t : ts) : rest -> stepWith t (state {stStack = Block ts : rest})
    Block [] : rest -> step (state {stStack = rest})
    If thenBranch elifBranches elseBranch : rest ->
      let cond = Eq (evalVar "?" state) (Lit "0")
          notCond = Not cond
          thenFork =
            state
              { stStack = Block thenBranch : rest,
                stConstraints = cond : stConstraints state
              }
          elseFork = case elifBranches of
            ((c, t) : otherElifBranches) ->
              state
                { stStack =
                    Block c :
                    If t otherElifBranches elseBranch :
                    rest,
                  stConstraints = notCond : stConstraints state
                }
            [] ->
              state
                { stStack = Block elseBranch : rest,
                  stConstraints = notCond : stConstraints state
                }
       in newExplorationState {exActive = [thenFork, elseFork]}
    [] -> newExplorationState {exDone = [state]}

exploreOnce :: ExplorationState -> ExplorationState
exploreOnce state =
  let nextStates = map step (exActive state)
   in foldl mergeExplorationStates (state {exActive = []}) nextStates

explore :: Maybe Int -> ExplorationState -> ExplorationState
explore maxActive state =
  let nActive = length (exActive state)
   in if nActive == 0 || maybe False (nActive >) maxActive
        then state
        else explore maxActive (exploreOnce state)

data Options = Options
  { opPath :: String,
    opMaxActive :: Maybe Int
  }
  deriving (Show)

optionsParser :: Parser Options
optionsParser =
  Options
    <$> argument str (metavar "PATH")
    <*> optional (option auto (long "max-active"))

mainImpl :: Options -> IO ()
mainImpl options = do
  contents <- readFile (opPath options)
  parseResult <- parseScript sys newParseSpec {psScript = contents}
  case prRoot parseResult of
    Just root ->
      let initial = newExplorationState {exActive = [initialState root]}
          state = explore (opMaxActive options) initial
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

main :: IO ()
main = mainImpl =<< execParser (info (optionsParser <**> helper) fullDesc)

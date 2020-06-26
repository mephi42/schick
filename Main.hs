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

data Link t
  = Sibling t
  | Parent t
  deriving (Show)

instance Functor Link where
  fmap f (Sibling t) = Sibling (f t)
  fmap f (Parent t) = Parent (f t)

type Links = Map.Map Id (Link Token)

data Cfg = Cfg
  { cfEntry :: Token,
    cfLinks :: Links
  }
  deriving (Show)

updateCfg :: Token -> Cfg -> Cfg
updateCfg token cfg =
  let link :: [Token] -> Cfg -> Cfg
      link (t0 : t1 : ts) cfg =
        let updatedLinks = Map.insert (getId t0) (Sibling t1) (cfLinks cfg)
         in link (t1 : ts) (updateCfg t0 (cfg {cfLinks = updatedLinks}))
      link [t0] cfg =
        let updatedLinks = Map.insert (getId t0) (Parent token) (cfLinks cfg)
         in updateCfg t0 (cfg {cfLinks = updatedLinks})
      link [] cfg = cfg
      linkBranches :: [(CaseType, [Token], [Token])] -> Cfg -> Cfg
      linkBranches ((CaseBreak, _, ts) : otherBranches) cfg =
        linkBranches otherBranches (link ts cfg)
      linkBranches [] cfg = cfg
   in case token of
        T_Annotation _ _ t -> link [t] cfg
        T_Script _ _ ts -> link ts cfg
        T_Pipeline _ [] [t] -> link [t] cfg
        T_Redirecting _ [] t -> link [t] cfg
        T_CaseExpression _ _ branches -> linkBranches branches cfg
        _ -> cfg

buildCfg :: ParseResult -> Maybe Cfg
buildCfg parseResult =
  fmap
    ( \root ->
        updateCfg
          root
          ( Cfg
              { cfEntry = root,
                cfLinks = Map.empty
              }
          )
    )
    (prRoot parseResult)

getSuccessor :: Cfg -> Token -> Maybe Token
getSuccessor cfg token = case Map.lookup (getId token) (cfLinks cfg) of
  Just (Sibling sibling) -> Just sibling
  Just (Parent parent) -> getSuccessor cfg parent
  Nothing -> Nothing

data Value
  = Lit String
  | Var String
  | Glob String
  | Concat [Value]
  | Matches Value Value
  | Not Value
  | Any Token
  deriving (Show)

data State = State
  { stCurrent :: Token,
    stVars :: Map.Map String Value,
    stConstraints :: [Value]
  }
  deriving (Show)

initialState :: Cfg -> State
initialState cfg =
  State
    { stCurrent = cfEntry cfg,
      stVars = Map.empty,
      stConstraints = []
    }

data ExplorationState = ExplorationState
  { exActive :: [State],
    exDone :: [State],
    exFailed :: [State]
  }
  deriving (Show)

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
  Maybe Token ->
  Value ->
  [(CaseType, [Token], [Token])] ->
  [Value] ->
  State ->
  ExplorationState ->
  ExplorationState
forkCase maybeCaseSuccessor word branches constraints state explorationState =
  let goToCaseSuccessor :: [Value] -> ExplorationState
      goToCaseSuccessor constraints = case maybeCaseSuccessor of
        Just caseSuccessor ->
          addActive
            ( state
                { stCurrent = caseSuccessor,
                  stConstraints = constraints
                }
            )
            explorationState
        Nothing ->
          addDone
            (state {stConstraints = constraints})
            explorationState
   in case branches of
        (CaseBreak, pattern' : otherPatterns, tokens) : otherBranches ->
          let matches = Matches word (eval pattern' state)
           in forkCase
                maybeCaseSuccessor
                word
                ((CaseBreak, otherPatterns, tokens) : otherBranches)
                (Not matches : constraints)
                state
                ( case tokens of
                    (token : _) ->
                      addActive
                        ( state
                            { stCurrent = token,
                              stConstraints = matches : constraints
                            }
                        )
                        explorationState
                    [] -> goToCaseSuccessor (matches : constraints)
                )
        (CaseBreak, [], _) : otherBranches ->
          forkCase
            maybeCaseSuccessor
            word
            otherBranches
            constraints
            state
            explorationState
        [] -> goToCaseSuccessor constraints
        incomplete -> error (unpack (pShowNoColor incomplete))

step :: Cfg -> State -> ExplorationState
step cfg state =
  let currentToken = stCurrent state
      maybeSuccessor = getSuccessor cfg currentToken
      ok :: State -> ExplorationState
      ok state = case maybeSuccessor of
        Just successor ->
          newExplorationState
            { exActive = [state {stCurrent = successor}]
            }
        Nothing -> newExplorationState {exDone = [state]}
   in case currentToken of
        T_Annotation _ _ t -> step cfg (state {stCurrent = t})
        T_Script _ _ (t : _) -> step cfg (state {stCurrent = t})
        T_Pipeline _ [] [t] -> step cfg (state {stCurrent = t})
        T_Redirecting _ [] t -> step cfg (state {stCurrent = t})
        T_SimpleCommand
          _
          [T_Assignment _ Assign var [] t]
          [] -> ok (assign var t state)
        T_CaseExpression _ word branches ->
          forkCase
            maybeSuccessor
            (eval word state)
            branches
            (stConstraints state)
            state
            newExplorationState
        _ -> newExplorationState {exFailed = [state]}

exploreOnce :: Cfg -> ExplorationState -> ExplorationState
exploreOnce cfg state =
  let nextStates = map (step cfg) (exActive state)
   in foldl mergeExplorationStates (state {exActive = []}) nextStates

explore :: Cfg -> ExplorationState -> ExplorationState
explore cfg state =
  if null (exActive state) then state else explore cfg (exploreOnce cfg state)

pPrintLinks :: Links -> IO ()
pPrintLinks =
  Map.foldMapWithKey
    (\k v -> putStrLn (show k ++ " -> " ++ show (fmap getId v)))

main :: IO ()
main = do
  contents <- readFile "gcc/config.gcc"
  parseResult <- parseScript sys newParseSpec {psScript = contents}
  case buildCfg parseResult of
    Just cfg ->
      let state =
            explore cfg (newExplorationState {exActive = [initialState cfg]})
       in do
            putStrLn "Links:"
            pPrintLinks (cfLinks cfg)
            putStrLn "Active:"
            mapM_ pPrint (exActive state)
            putStrLn "Done:"
            mapM_ pPrint (exDone state)
            putStrLn "Failed:"
            mapM_ pPrint (exFailed state)
    Nothing -> putStrLn "Couldn't parse"

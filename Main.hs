{-# LANGUAGE PatternSynonyms #-}

module Main where

import qualified Data.Map as Map (Map, empty, insert, lookup)
import Data.Maybe (fromMaybe)
import ShellCheck.AST
  ( AssignmentMode (..),
    Id,
    InnerToken (..),
    Token (..),
    getId,
    pattern T_Annotation,
    pattern T_Assignment,
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
import Text.Pretty.Simple (pPrint)

sys :: SystemInterface IO
sys =
  SystemInterface
    { siReadFile = const (return (Left "Not implemented")),
      siFindSource = \_ _ sourcedFile -> return sourcedFile,
      siGetConfig = const (return Nothing)
    }

data Link
  = Sibling Token
  | Parent Token
  deriving (Show)

data Cfg = Cfg
  { cfEntry :: Token,
    cfLinks :: Map.Map Id Link
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
   in case token of
        T_Annotation _ _ t -> link [t] cfg
        T_Script _ _ ts -> link ts cfg
        T_Pipeline _ [] [t] -> link [t] cfg
        T_Redirecting _ [] t -> link [t] cfg
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

data Value = Literal String | Any Token deriving (Show)

data State = State
  { stCurrent :: Token,
    stVars :: Map.Map String Value
  }
  deriving (Show)

initialState :: Cfg -> State
initialState cfg =
  State
    { stCurrent = cfEntry cfg,
      stVars = Map.empty
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

assign :: String -> Token -> State -> State
assign var t state =
  let val = case t of
        T_Literal _ val -> Literal val
        T_NormalWord _ [T_Literal _ val] -> Literal val
        T_NormalWord _ [T_SingleQuoted _ val] -> Literal val
        _ -> Any t
   in state {stVars = Map.insert var val (stVars state)}

step :: Cfg -> State -> ExplorationState
step cfg state =
  let currentToken = stCurrent state
      ok :: State -> ExplorationState
      ok state = case getSuccessor cfg currentToken of
        Just link -> newExplorationState {exActive = [state {stCurrent = link}]}
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
        _ -> newExplorationState {exFailed = [state]}

exploreOnce :: Cfg -> ExplorationState -> ExplorationState
exploreOnce cfg state =
  let nextStates = map (step cfg) (exActive state)
   in foldl mergeExplorationStates (state {exActive = []}) nextStates

explore :: Cfg -> ExplorationState -> ExplorationState
explore cfg state =
  if null (exActive state) then state else explore cfg (exploreOnce cfg state)

main :: IO ()
main = do
  contents <- readFile "gcc/config.gcc"
  parseResult <- parseScript sys newParseSpec {psScript = contents}
  case buildCfg parseResult of
    Just cfg ->
      let state =
            explore cfg (newExplorationState {exActive = [initialState cfg]})
       in do
            putStrLn "Active:"
            mapM_ pPrint (exActive state)
            putStrLn "Done:"
            mapM_ pPrint (exDone state)
            putStrLn "Failed:"
            mapM_ pPrint (exFailed state)
    Nothing -> putStrLn "Couldn't parse"

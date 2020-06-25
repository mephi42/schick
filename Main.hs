module Main where

import qualified Data.Map as Map (Map, empty, insert, lookup)
import Data.Maybe (fromMaybe)
import ShellCheck.AST (Id, InnerToken (..), Token (..), getId)
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

type TokenMap = Map.Map Id Token

type EdgeMap = Map.Map Id [Token]

data Cfg = Cfg
  { cfEntry :: Token,
    cfTokenMap :: TokenMap,
    cfSuccessors :: EdgeMap
  }
  deriving (Show)

insertTokens :: Token -> TokenMap -> TokenMap
insertTokens token@(OuterToken id _) = Map.insert id token

pr2cfg :: ParseResult -> Maybe Cfg
pr2cfg pr =
  fmap
    ( \root ->
        Cfg
          { cfEntry = root,
            cfTokenMap = insertTokens root Map.empty,
            cfSuccessors = Map.empty
          }
    )
    (prRoot pr)

getSuccessors :: Cfg -> Token -> [Token]
getSuccessors cfg token = fromMaybe [] (Map.lookup (getId token) (cfSuccessors cfg))

newtype Value = Literal String deriving (Show)

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

step :: Cfg -> State -> ExplorationState
step cfg state = case getSuccessors cfg (stCurrent state) of
  [successor] ->
    newExplorationState
      { exActive = [state {stCurrent = successor}]
      }
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
  case pr2cfg parseResult of
    Just cfg ->
      let state =
            explore
              cfg
              ( newExplorationState
                  { exActive = [initialState cfg]
                  }
              )
       in do
            putStrLn "Active:"
            mapM_ pPrint (exActive state)
            putStrLn "Done:"
            mapM_ pPrint (exDone state)
            putStrLn "Failed:"
            mapM_ pPrint (exFailed state)
    Nothing -> putStrLn "Couldn't parse"

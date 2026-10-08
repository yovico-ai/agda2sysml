module Main (main) where

import Agda.Main (runAgda')
import Agda2SysML.Compiler (backend)
import Agda2SysML.Workflow (run, options)
import Control.Exception (IOException, catch)
import Options.Applicative
import System.Environment (getArgs, withArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    "_agda":rest -> withArgs rest (runAgda' [backend])
    _ -> (execParser cli >>= run) `catch` failure
  where
    cli = info (options <**> helper <**> infoOption "agda2sysml 0.1.0 (Agda 2.8.0)" (long "version"))
      (fullDesc <> progDesc "Generate traceable SysML from a checked Agda project")
    failure :: IOException -> IO ()
    failure e = hPutStrLn stderr (show e) >> exitFailure

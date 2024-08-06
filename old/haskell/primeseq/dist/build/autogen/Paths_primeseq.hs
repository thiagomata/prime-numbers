{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_primeseq (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/thiago-rokt/.cabal/bin"
libdir     = "/home/thiago-rokt/.cabal/lib/x86_64-linux-ghc-8.6.5/primeseq-0.1.0.0-9TsdX2FN7N634STrVB6TVr"
dynlibdir  = "/home/thiago-rokt/.cabal/lib/x86_64-linux-ghc-8.6.5"
datadir    = "/home/thiago-rokt/.cabal/share/x86_64-linux-ghc-8.6.5/primeseq-0.1.0.0"
libexecdir = "/home/thiago-rokt/.cabal/libexec/x86_64-linux-ghc-8.6.5/primeseq-0.1.0.0"
sysconfdir = "/home/thiago-rokt/.cabal/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "primeseq_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "primeseq_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "primeseq_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "primeseq_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "primeseq_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "primeseq_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)

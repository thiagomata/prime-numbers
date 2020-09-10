# primeseq

## To run the tests

```
    stack test
```

### To build

```
    rm -rf dist-newstyle
    cabal build -O
```

### To interact

```
    ghci
    :cd src
    :load Lib
    -- now you can run your commands
    firstPrimes "fuse-better" 10
```

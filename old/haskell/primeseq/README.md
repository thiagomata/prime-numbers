# primeseq

## To run the tests

```
    stack test
```

### To build

```bash
    
    # remove cache
    rm -rf dist-newstyle
    
    # create the binary program
    cabal build -O
    
    # find the program
    find . -name "primeseq"
```

### To play in the interact GHCI

```haskell
    $ ghci
    :cd src
    :load Lib
    -- now you can run your commands
    firstPrimes "fuse-better" 10
```

### Run the tests
```bash

    $ time ./primeseq "fuse-inverted" 1000 | md5sum
    # 4bf5485d099fc858d97e679a08ff293a  -
    # ./primeseq "fuse-inverted" 1000  0.83s user 0.19s system 818% cpu 0.124 total

    $ time ./primeseq "sequence" 1000 | md5sum
    # 4bf5485d099fc858d97e679a08ff293a  -
    # "sequence" 1000  0.12s user 0.15s system 549% cpu 0.049 total

    $ time ./primeseq "classic" 1000 | md5sum
    # 4bf5485d099fc858d97e679a08ff293a  -
    # ./primeseq "classic" 1000  11.48s user 3.61s system 1004% cpu 1.502 total

    $ time ./primeseq "fuse-better" 1000 | md5sum
    # 4bf5485d099fc858d97e679a08ff293a  -
    # ./primeseq "fuse-better" 1000  0.39s user 0.08s system 600% cpu 0.077 total
```

# building and cleaning

## `haskell`

### build

```bash
$ cd sh/haskell
$ ./build.sh
```

an executable is generated in `bin/run/haskell`

you can run the executable interactively, or, for example using

./Incremental-NC-Coins --incremental 8
./Incremental-NC-Coins --coins 8 3
./Incremental-NC-Coins --stream 8
./Incremental-NC-Coins --stream 8 25
./Incremental-NC-Coins --stream-coins 8 3
./Incremental-NC-Coins --stream-coins 8 3 25
./Incremental-NC-Coins --demo-laziness 1000000 500 100

### clean

```bash
$ cd sh/haskell
$ ./clean.sh
$ cd ..
```

the executable in `bin/run/haskell` is removed

## `julia`

### build

```bash
$ cd sh/julia
$ ./build.sh
$ cd ..
```
an executable is generated in `bin/run/julia`

you can run the executable interactively, or, for example using

./Incremental-NC-Coins --incremental 8
./Incremental-NC-Coins --coins 8 3

### clean

```bash
$ cd sh/julia
$ ./clean.sh
$ cd ..
```

the executable in `bin/run/julia` is removed

## `lean`

### build

```bash
$ cd sh/lean
$ ./build.sh
$ cd ..
```

an executable is generated in `bin/run/lean`

### clean

```bash
$ cd sh/lean
$ ./clean.sh
$ cd ..
```
the executable in `bin/run/lean` is removed

## `tex`

### build

```bash
$ cd sh/tex
$ ./build.sh
$ cd ..
```

a pdf file is generated in `bin/doc/pdf`

nothing to run :-) just read it

### clean

```bash
$ cd sh/lean
$ ./clean.sh
$ cd ..
```
the pdf file in `bin/doc/pdf` and other artifacts are removed

# patron
Bug Pattern Matching Tool using SMT Solver for Patch Transplantation

## Usage

**Bug Pattern Construction**
```
./patron db <target project directory>
```
- The target project dir must have the following structure
```
target_dir
    ├--bug
    │   ├ x.c
    │   └ sparrow-out 
    └--patch      ├ ...
        ├ y.c
        └ sparrow-out 
                ├ ...
```
**Patch Generation**
```
./patron patch <Donee directory> <DB directiory>
```
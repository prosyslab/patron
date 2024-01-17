# patron
Bug Pattern Matching Tool using SMT Solver for Patch Transplantation

## Prerequisites
- Opam
- Sparrow
- Target C program taint-analyzed by Sparrow
- One True Alarm # from `<target_bug_dir>/sparrow-out/taint/datalog/Alarm.map`
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
## Usage

```
./patron <target project directory> <True Alarm #>
```

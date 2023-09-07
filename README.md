# Mophasco (MOnadic framework for PHAsed name resolution using SCOpe graphs)

This archive contains the code accompanying the paper.
> Casper Bach Poulsen, Aron Zwaan, Paul Hübner. 2023. “A Monadic Framework for Name Resolution in Multi-Phased Type Checkers”. In Proceedings of the 22nd ACM SIGPLAN International Conference on Generative Programming: Concepts and Experiences (GPCE '23), October 22--23, 2023, Cascais, Portugal. https://doi.org/10.1145/3624007.3624051

The purpose of this readme is to provide execution instructions, and relate the code to the content of the paper.

## Dependencies

The code can be executed using
- GHC 9.4.4.
- Cabal 3.8.1.0
or higher

## Execution

Running `cabal test` build the project and executes the tests.
These tests include the tests of LM, and tests of the `SG` and `Critical` effects (discussed below).

## Correspondence to Paper.

### Preliminaries

As briefly discussed in the paper, the abstract monad _m_ is constructed using _Hefty Algebra's_ (due to Poulsen and Van der Rest (2023)).
As such, the unspecified monad type _m_ in the paper is instantiated to `Hefty h`, where `h` is the sum of the effects used in the program.
The specification of hefty algebra's can be found in `./src/Hefty.hs`.

All effects have (at least) two additional type level parameters:
- `m` is the underlying computation type
- `k` is a continuation
In contrast to the paper, all constructors usually have a continuation as a last argument.
All effects typically have a smart constructor, that injects the effect into a larger sum of effectful operations.
These typically have signatures like `err :: Error e < h => e -> Hefty h a` (from `src/Hefty/Op/Error.hs`), which corresponds to the signatures _err :: String -> m a_ in the paper
Finally, handlers (names typically starting with an `h`, e.g. `hErr`) assign semantics to the operations defined in an effect.

### Scope Graphs

The interface for scope graph operations discussed in §2.3 and §3.1 can be found in `src/Hefty/Op/Scope.hs`.
The 'precise' handler is implemented in `src/Hefty/Op/Scope/Strong.hs`, while the variant based on overapproximation of critical edges is found in `src/Hefty/Op/Scope/Weak.hs`.
Both modules define their own `Graph` data type.

### Functor Composition

The _Monoidal_ type class in §4.1 is called `Monplicative` in our implementation, and can be found in `src/Data/Functor/Monplicative.hs`.
The functor composition type _f . g_ (§4.1) is implemented in `src/Data/Functor/Comp.hs` (where the composition operator is `:.:`).
In the same module, the phased computation operators from §4.3 can be found.

The example given in fig. 3 is discussed below.

### Case Study Preliminaries

The case studies rely of some reusable data types and effects:
- `src/Data/Term` defines first order terms
- `src/Hefty/Op/Term/Exists.hs` defines the `Exists` effect, which allows generation of free meta-variables.
- `src/Hefty/Op/Term/Equals.hs` defines the `Equals` effect, which allows unifying and inspecting terms.
In the paper, the `Exists` and the `Equals` effect are combined in the _Unif_ type class.

- `src/Hefty/Op/Error.hs` contains the _Err_ operation (§4.4), allowing abrupt termination of a computation.
- `src/Hefty/Op/State.hs` contains the _State_ operation, which is similar to the well-known `State` monad.

### Case Study 1: MiniML

The implementation of MiniML discussed in §5.1 can be found in `src/Lang/MiniML.hs`.
A major difference with the code presented in the paper is that let bindings allow pattern matching on tuples (e.g. `let (x, y) = (1, 2) in x + y`), where each variable in the pattern (not the pattern as a whole) is generalized.
Therefore, binding constructs traverse the left-hand-side pattern, generalize the corresponding right hand side type if needed (let bindings only), and create separate declarations in the scope graph. This is implemented in the `tpat` and `spat` traversals, for monomorphic and polymorphic binds, respectively.
Here, the `spat` function inlined in the `Let` case of `miniml` rougly corresponds to the case shown in the paper.

### Case Study 2: LM

The implementation of LM discussed in §5.2 can be found in `src/Lang/LM.hs`.
The `lm` function roughly corresponds to `mdec` in Figure 3.
The `imports` function implements the permutation-based import resolution policy described in §5.2.

The `AnyOrder` effect can be found in `src/Hefty/Op/Scope/AnyOrder.hs`.
As this effect is higher-order, it does not contain handlers, but rather an _elaborator_, which transform the higher-order operations into either other higher-order operations, or first-order (algebraic) operations.
In this case, the `eAnyOrd2Crit` function elaborates the `AnyOrder` effect to the `Critical` effect, which is defined in `src/Hefty/Op/Scope/Critical.hs`.
Again, this higher-order effect uses elaborators.
The `eSC` function transforms the `query` operations to disable adding stability information (residual queries or closed edges), and adding them to the query cache.
The `eCritical` elaborator inserts a `State` effect containing a cache with executed queries to capture the results of the `eSC` elaboration.
Then it 'marks' the current scope graph for future reference (`g`).
The the initial computation (`t`) is successful, the `go` function verifies all queries in the cache (`ch`).
If that succeeds, the continuation `k` is invoked with the result of `t` (`r`), otherwise the scope graph operations performed by `t` are undone (rollbacked) and the error handler is invoked.
This is used by `eAnyOrd2Crit` as follows.
It first computes all permutations of the list of computations in the first argument.
Then it tries each of those.
When a computation succeeds, the next one within the same permutation is tried.
If all computations have succeeded, this permutation was correct, and a success is returned.
It a computation fails, the block is exited, and the next permutation is tried.

Test cases are found in `./test/programs/lm`, loaded using the ATerm (Annotated TERM format) library in `./aterm`.

## References

- Casper Bach Poulsen and Cas van der Rest. 2023. Hefty Algebras: Modular Elaboration of Higher-Order Algebraic Effects. Proc. ACM Program. Lang. 7, POPL, Article 62 (January 2023), 31 pages. https://doi.org/10.1145/3571255

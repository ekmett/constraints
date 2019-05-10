0.11 [2019.05.10]
-----------------
* Introduce a `HasDict` type class for types that witness evidence of
  constraints, such as `Dict`, `(:-)`, `Coercion`, `(:~:)`, `(:~~:)`, and
  `TypeRep`.
* Generalize the types of `withDict` and `(\\)` to be polymorphic over
  any `HasDict` instance.
* Add `type (⊢) = (:-)`.
* Fix unsafe mistakes in the statements of `dividesDef` and `timesDiv` in
  `Data.Constraint.Nat`.
* Make the implementations of `Min` and `Max` reduce on more inputs in
  `Data.Constraint.Nat`.
* Add `minusNat` and `minusZero` functions to `Data.Constraint.Nat`.
* Support `hashable-1.3.*` and `semigroups-0.19.*`.

0.10.1 [2018.07.02]
-------------------
* Allow building with GHC 8.6.
* Add three axioms about `(+)` and `(-)` to `Data.Constraint.Nat`.

0.10
----
* Adapt to the `Semigroup`–`Monoid` Proposal (introduced in `base-4.11`):
  * Add a `Semigroup` instance for `Dict`
  * Add the appropriate `(:=>)` instances involving `Semigroup`, and change the
    `Class () (Monoid a)` instance to `Class (Semigroup a) (Monoid a)` when
    `base` is recent enough
  * Add the appropriate `Lifting(2)` instances involving `Semigroup`
* `Data.Constraint.Nat` now reexports the `Div` and `Mod` type families from
  `GHC.TypeLits` on `base-4.11` or later
* Fix the type signature of `maxCommutes`
* Export the `no` method of `Bottom`
* Add `NFData` instances for `Dict` and `(:-)`

0.9.1
-----
* Correct an improper use of `unsafeCoerce` in the internals of
  `Data.Constraint.Nat` and `Data.Constraint.Symbol`
* Correctly identify the mismatched types when you defer an unsatisfiable
  equality constraint through `Data.Constraint.Deferrable`
* Re-export the `(:~~:)` defined in `base` from `Data.Constraint.Deferred` with
  GHC 8.2 or later
* Add several new `(:=>)` instances for `Bits`, `Identity`, `Const`, `Natural`,
  `IO`, and `Word`.
* Modernize some existing `Class` and `(:=>)` instances to reflect the fact
  that `Applicative` is now a superclass of `Monad` on recent versions of
  `base`.

0.9
---
* Changes to `Data.Constraint`:
  * Add `strengthen1` and `strengthen2`
* Changes to `Data.Constraint.Deferrable`:
  * Add a `Deferrable ()` instance
  * The `Deferrable (a ~ b)` instance now shows the `TypeRep`s of `a` and `b`
    when a type mismatch error is thrown
  * Add `defer_` and `deferEither_`, counterparts to `defer` and `deferEither`
    which do not require proxy arguments
  * Enable `PolyKinds`. This allows the `Deferrable (a ~ b)` instance to be
    polykinded on all supported versions of GHC _except_ 7.10, where the kinds
    must be `*` due to an old GHC bug
  * Introduce a heterogeneous equality type `(:~~:)`, and use it to define a
    `Deferrable (a ~~ b)` instance on GHC 8.0 or later
* Changes to `Data.Constraint.Forall`:
  * Implement `ForallF` and `ForallT` in terms of `Forall`
  * Add `ForallV` and `InstV` (supporting a variable number of parameters)
  * Add a `forall` combinator
* Introduce `Data.Constraint.Nat` and `Data.Constraint.Symbol`, which contain
  utilities for working with `KnownNat` and `KnownSymbol` constraints,
  respectively. These modules are only available on GHC 8.0 or later.

0.8
-----
* GHC 8 compatibility
* `transformers` 0.5 compatibility
* `binary` 0.8 compatibility
* Dropped support for GHC 7.6 in favor of a nicer Bottom representation.

0.7
---
* Found a nicer encoding of the initial object in the category of constraints using a [nullary constraint](https://ghc.haskell.org/trac/ghc/ticket/7642).

0.6.1
-----
* Remove the need for closed type families from the new `Forall`.

0.6
---
* Completely redesigned `Data.Constraint.Forall`. The old design is unsound and can be abused to define `unsafeCoerce`!
  The new design requires closed type families, so this module now requires GHC 7.8+

0.5.1
-----
* Added `Data.Constraint.Deferrable`.

0.5
-----
* Added `Data.Constraint.Lifting`.

0.4.1.3
-------
* Acknowledge we actually need at least base 4.5

0.4.1.2
-------
* Restore support for building on older GHCs

0.4.1.1
-------
* Minor documentation fixes.

0.4.1
-----
* Added `mapDict` and `unmapDict`.
* Added a lot of documentation.

0.4
---
* `Typeable` and `Data`. The `Data` instance for `(:-)` is a conservative approximation that avoids having to turn (:-) into a cartesian closed category.
  If it becomes a pain point for users, I know how to do that, and have done so in other libraries -- see [hask](http://github.com/ekmett/hask), but I'm hesitant to bring such heavy machinery to bear and it isn't clear how to do it in a way that is compatible with those other libraries.

0.3.5
-----
* Explicit role annotations

0.3.4.1
-------
* Fixed build failures.
* Fixed an unused import warning on older GHCs.

0.3.4
-----
* Added `bottom`

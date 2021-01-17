# Changelog
## 1.0.0.0
* Drops Peano-numerals
* Obsolete kind-generic classes
* Now all types are kinded with GHC's builtin type-level naturals, and no type parameters for naturals.
* Drops dependency for `singletons` package and their relatives.

## 0.9.0.0
* This is transitional change: preparation for future rework of `type-natural`
  - Types and constraints in `Data.Sized.Builtin` is now incompatible with `Data.Sized` and `Data.Sized.Peano`
  - The latter two modules will be removed in future release.
* Removes `NilL` and `NilR`
* Compolete overhaul on `Data.Sized.Builtin`
  - Stop using orders from `Data.Singletons`
  - Types of nested pattern synonyms can now be inferred correctly

## 0.8.0.0
* Makes `sLength` using `KnownNat` instance to get O(1) always.
* Introduces `Nil` pattern and deprecates `NilL` and `NilR`.
* Previously, in sepcialised modules for `Builtin` and `Peano`,
  `elemIndex`, `elemIndices` and their Ordinal version were misimplemented;
  they are now correctly uses their counterparts in `Data.Sized`.
* Adds documentation for specialised modules.

## 0.7.0.0
* Stop using `ListLike` package and switched to [`subcategories`] package for the abstraction of sequential types.
* Complete overhaul on type signatures.
* Both `Data.Sized.Builtin` and `Data.Sized.Peano` exports specialised functions instead of reexporting functions from `Data.Sized`.

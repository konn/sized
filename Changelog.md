# Changelog
## 0.8.0.0
* Makes `sLength` using `KnownNat` instance to get O(1) always.

## 0.7.0.0
* Stop using `ListLike` package and switched to [`subcategories`] package for the abstraction of sequential types.
* Complete overhaul on type signatures.
* Both `Data.Sized.Builtin` and `Data.Sized.Peano` exports specialised functions instead of reexporting functions from `Data.Sized`.
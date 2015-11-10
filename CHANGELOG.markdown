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

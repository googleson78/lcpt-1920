## Emacs cheat sheet
* eval expr - `C-x C-e`
* `x` - `C-d`
* `d$` - `C-k`
* `u` - `C-x u`
* `p` - `C-y`
* kill buffer - `C-x k`
* `:w` - `C-x C-s`

## Logic connectives cheat sheet
* `split` - create a tuple (two new goals), used to eliminate conjunction

* nb: there is no primitive disjunction

* `display-global-assumptions` - show default axioms

* `use` creates a lambda for any (non-)dependent pi type (so it can be used for `all x.` elim)

* `ex-elim`
  traditional ex equivalence - `(ex x. P x) -> C` is the same as `(forall x. P x -> C) -> C`

  use to dispatch ex

* `ex-intro`
  sigma constructor, needs an argument - e.g. `(ex-intro (pt "n"))` will construct `< n , _ >`

  (pt - parse term)


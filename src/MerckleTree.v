Require Import List String.
Open Scope string_scope.

Variable data hash : Set.
Variable gen_hash : data -> hash.
Variable concat : hash -> hash -> data.

Inductive mtree : Set :=
| L : data -> mtree
| N : mtree -> mtree -> mtree
.

Inductive MTree : nat -> hash -> mtree -> Prop :=
| MTL : forall data, MTree 0 (gen_hash data) (L data)
| MTN : forall n h1 h2 left right,
    MTree n h1 left -> MTree n h2 right ->
    MTree (1 + n) (gen_hash (concat h1 h2)) (N left right)
.

Require Import List String.
Require Import Result.
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

Fixpoint hash_of_tree t :=
  match t with
  | L data => gen_hash data
  | N left_ right_ =>
    gen_hash (concat (hash_of_tree left_) (hash_of_tree right_))
  end.

Definition path := list bool.
Definition len (p: path) : nat := List.length p.

Inductive proof :=
| Mk_proof : data -> list hash -> proof.

Definition lenp '(Mk_proof data pstream) := List.length pstream.

Definition p_data '(Mk_proof data pstream) := data.
Definition p_stream '(Mk_proof data pstream) := pstream.

Fixpoint verifier (path: path) (proof: proof) :=
  match path with
  | nil =>
    Ok (gen_hash (p_data proof))
  | bit :: path' =>
    match p_stream proof with
    | nil => Error ""
    | hd :: tl =>
      verifier path' (Mk_proof (p_data proof) tl) >>= fun h' =>
      if bit then
        Ok (gen_hash (concat h' hd))
      else
        Ok (gen_hash (concat hd h'))
    end
  end.


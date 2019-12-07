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

Fixpoint prover (path:path) (tree : mtree) :=
  match path with
  | nil =>
    match tree with
    | L data => Ok (Mk_proof data nil)
    | N _ _ => Error tt
    end
  | bit :: path' =>
    match tree with
    | L _ => Error tt
    | N left_ right_ =>
      if bit then
        prover path' left_ >>= fun '(Mk_proof data pstream) =>
        let hr := hash_of_tree right_ in
        Ok (Mk_proof data (hr :: pstream))
      else
        prover path' right_ >>= fun '(Mk_proof data pstream) =>
        let hl := hash_of_tree left_ in
        Ok (Mk_proof data (hl :: pstream))
    end
  end.

Lemma length_prover : forall path h (tree : mtree) proof,
    MTree (len path) h tree ->
    prover path tree = Ok proof ->
    lenp proof = len path.
Proof.
  intros path. induction path; intros h tree proof Htree.
  - inversion Htree. injection 1. intros Hproof. now subst proof.
  - inversion Htree. simpl.
    destruct a.
    +
      case_eq (prover path0 left); [|now auto]. intros proof' Hproof'.
      simpl. destruct proof'. injection 1. intros Hproof. subst.
      now rewrite <- (IHpath h1 left (Mk_proof d l)).
    +
      case_eq (prover path0 right); [|now auto]. intros proof' Hproof'.
      simpl. destruct proof'. injection 1. intros Hproof. subst.
      now rewrite <- (IHpath h2 right (Mk_proof d l)).
Qed.


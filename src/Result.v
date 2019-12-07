Inductive result (A Err : Set) : Set :=
| Ok : A -> result A Err
| Error : Err -> result A Err.
Arguments Ok [A Err].
Arguments Error [A Err].

Definition bind {A B Err : Set} (m: result A Err) (f: A -> result B Err) :=
  match m with
  | Ok x => f x
  | Error err => Error err
  end.

Infix ">>=" := bind (at level 60).

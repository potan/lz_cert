
Require Import String.
Require List.

Open Scope string_scope.
Open Scope list_scope.


Definition buffer (size: nat) (buf input: string) :=
    let tot := append buf input in
    let off := length tot - size in
    substring off size tot.

Compute (buffer 8 "qwertyui" "asdf").


Inductive Out: Set := Str: string -> Out | Ref: nat -> nat -> Out.

Axiom undefined: False.

Definition err {A: Type} : A :=
   match undefined return A with
   end.


Fixpoint skipper (bufsize: nat) (buf acc win : string)
         : (string * string * string * nat) :=
   match win with
   | "" => (acc, buf, win, 0)
   | String c nwin =>
       let p := String c "" in
       let nbuf := buffer bufsize buf p in
       match index 0 nwin nbuf with
       | None => skipper bufsize nbuf (append acc p) nwin
       | Some i => (append acc p, nbuf, nwin, i)
       end
   end.

Compute (skipper 30 "caaaaa" "" "baaaa").


Fixpoint lz
   (min bufsize: nat)
   (input: string)
   (acc: list Out)
   (buf: string)
   (win: string)
   (off: nat)
      : list Out :=
    match input with
    | "" => List.rev (match win with
                      | "" => acc
                      | String _ _ =>
                           (if Nat.ltb min (length win)
                            then Ref (length buf - off) (length win)
                            else Str win
                           ) :: acc
                      end)
    | String c s =>
             let nwin := append win (String c "") in
             match index 0 nwin buf with
             | Some noff => lz min bufsize s acc buf nwin noff
             | None =>  match skipper bufsize buf "" nwin with
                        | (out, nnbuf, nnwin, nnoff) =>
                            let nacc :=
                              if Nat.ltb min (length win)
                              then
                                Str out :: Ref (length buf - off) (length win) :: acc
                              else
                                Str (append out win) :: acc
                            in lz min bufsize s nacc nnbuf nnwin nnoff
                        end
             end
     end.

Compute (lz 3 10 "" nil "aaaa" "aaaa" 0).

Example lzCheck1: lz 3 10 "aaaa" nil "aaaa" "" 0 = Ref 4 4 :: nil.
Proof.
 simpl.
 reflexivity.
Qed.

Compute (lz 3 10 "aaaaaaaaaaaaa" nil "" "" 0).

Fixpoint unlz (comp: list Out) (acc: string) : string :=
  match comp with
  | nil => acc
  | h :: t => unlz t (append acc
                (match h with
                 | Str s => s
                 | Ref off size => substring (length acc - off) size acc
                 end))
  end.

Compute (unlz (Str "qwertyui" :: Ref 4 3 :: Ref 5 4 :: nil) "").
Compute (lz 3 20 "qwertyuityuuity" nil "" "" 0).

Lemma lz_accum: forall (dat: string) (min size: nat) (buf win: string) (off: nat) (o: list Out),
   lz min size dat o buf win off = List.rev o ++ lz min size dat nil buf win off.
Proof.
  intros.
  unfold lz.
Abort.

Theorem lz_correct: forall (dat: string) (min size: nat),
     unlz (lz min size dat nil "" "" 0) "" = dat.
Proof.
  induction dat ; simpl.
  { reflexivity. }
  destruct size ; simpl ; unfold buffer ; simpl.
Abort.
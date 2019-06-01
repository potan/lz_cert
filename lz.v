
Require String.
Require List.

Compute (String.substring 3 1 "qwertyu").

Open Scope string_scope.
Open Scope list_scope.


Definition buffer (size: nat) (buf input: String.string) :=
    let tot := String.append buf input in
    let off := String.length tot - size in
    String.substring off size tot.

Compute (buffer 8 "qwertyui" "asdf").


Inductive Out: Set := Str: String.string -> Out | Ref: nat -> nat -> Out.

Axiom undefined: False.

Definition err {A: Type} : A :=
   match undefined return A with
   end.


Fixpoint skipper (bufsize: nat) (buf acc win : String.string)
         : (String.string * String.string * String.string * nat) :=
   match win with
   | "" => (acc, buf, win, 0)
   | String.String c nwin =>
       let p := String.String c "" in
       let nbuf := buffer bufsize buf p in
       match String.index 0 nwin nbuf with 
       | None => skipper bufsize nbuf (String.append acc p) nwin
       | Some i => (String.append acc p, nbuf, nwin, i)
       end
   end.

Compute (skipper 30 "caaaaa" "" "baaaa").


Fixpoint lz
   (min bufsize: nat)
   (input: String.string)
   (acc: list Out)
   (buf: String.string)
   (win: String.string)
   (off: nat)
      : list Out :=
    match input with
    | "" => List.rev (match win with
                      | "" => acc
                      | String.String _ _ =>
                           (if Nat.ltb min (String.length win)
                            then Ref (String.length buf - off) (String.length win)
                            else Str win
                           ) :: acc
                      end)
    | String.String c s =>
             let nwin := String.append win (String.String c "") in
             match String.index 0 nwin buf with
             | Some noff => lz min bufsize s acc buf nwin noff
             | None =>  match skipper bufsize buf "" nwin with
                        | (out, nnbuf, nnwin, nnoff) =>
                            let nacc :=
                              if Nat.ltb min (String.length win)
                              then
                                Str out :: Ref (String.length buf - off) (String.length win) :: acc
                              else
                                Str (String.append out win) :: acc
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

Fixpoint unlz (comp: list Out) (acc: String.string) : String.string :=
  match comp with
  | nil => acc
  | h :: t => unlz t (String.append acc
                (match h with
                 | Str s => s
                 | Ref off size => String.substring (String.length acc - off) size acc
                 end))
  end.

Compute (unlz (Str "qwertyui" :: Ref 4 3 :: Ref 5 4 :: nil) "").
Compute (lz 3 20 "qwertyuityuuity" nil "" "" 0).

Lemma lz_accum: forall (dat: String.string) (min size: nat) (buf win: String.string) (off: nat) (o: list Out),
   lz min size dat o buf win off = List.rev o ++ lz min size dat nil buf win off.
Proof.
  intros.
  unfold lz.
  
  
Theorem lz_correct: forall (dat: String.string) (min size: nat),
     unlz (lz min size dat nil "" "" 0) "" = dat.
Proof.
  induction dat ; simpl.
  { reflexivity. }
  destruct size ; simpl ; unfold buffer ; simpl.

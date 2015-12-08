Require Import Coq.Strings.String Coq.Lists.List Coq.Setoids.Setoid.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.MinimalParse.
Require Import Fiat.Common.List.Operations.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {G : grammar Char}.
  Context {predata : @parser_computational_predataT}
          {rdata' : @parser_removal_dataT' _ G _}.


  Lemma minimal_parse_of_drop_pred {len0 valid str n ls}
        (mp : minimal_parse_of (G := G) len0 valid str (drop n ls))
  : minimal_parse_of (G := G) len0 valid str (drop (pred n) ls).
  Proof.
    generalize dependent ls; induction n as [|n IHn]; intros; simpl.
    { assumption. }
    { destruct ls as [|x xs].
      { destruct n as [|n]; simpl in *; auto with nocore. }
      { destruct n as [|n]; simpl in *; [ | solve [ auto with nocore ] ].
        right; assumption. } }
  Defined.
End cfg.

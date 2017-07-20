Require Import Fiat.Parsers.Grammars.JavaScriptAssignmentExpression.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Refinement.DisjointRules.
Require Import Fiat.Parsers.Refinement.DisjointRulesRev.
Require Import Fiat.Parsers.ExtrOcamlParsers. (* for simpl rules for [find_first_char_such_that] *)
Require Import Fiat.Parsers.Refinement.BinOpBrackets.BinOpRules.
Require Import Fiat.Parsers.StringLike.String.

Set Ltac Profiling.
Section IndexedImpl.
  (*Context {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSI : StringIso Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {HSEP : StringEqProperties Ascii.ascii}
          {HSIP : StringIsoProperties Ascii.ascii}.*)

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec javascript_assignment_expression_pregrammar string_stringlike).
  Proof.

    Time start sharpening ADT.

    Reset Ltac Profile.
    eapply SharpenStep;
      [ solve [ apply FirstStep ] | ];
      unfold opt_rindexed_spec.
  (*
  let p' := fresh "p'" in
  match goal with
  | [ |- context[pregrammar_productions ?G] ]
    => let p := constr:(pregrammar_productions G) in
       set (p' := p);
       hnf in p'
  end; *)
    Time Timeout 5 lazymatch goal with
    | [ |- context[opt2.fold_right _ _ ?ls] ]
      => replace_with_vm_compute_by_set ls
    end.
    Print Ltac start_honing.
    Require Import DisjointLemmas PossibleTerminalsSets.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.StringLike.FirstChar Fiat.Parsers.StringLike.LastChar Fiat.Parsers.StringLike.ForallChars.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Precompute.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretationDefinitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Fix.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.AsciiLattice.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.ProdAbstractInterpretationDefinitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretation.
Require Import Fiat.Parsers.Refinement.EmptyLemmas.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.LogicFacts.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Common.

    Notation tree := (PositiveSet.Node _ _ _).
    Notation ls := (cons _ _).
    Definition hide {T} {v : T} := v.
    Notation TREE := (FMapPositive.PositiveMap.tree _).
    Time let G := get_grammar in
    lazymatch goal with
    | [ |- context[@ParserInterface.split_list_is_complete_idx _ G ?HSLM ?HSL] ]
      => pose (_ : @StringLikeProperties _ HSLM HSL)
    end;
      lazymatch goal with
      | [ H : possible_data G |- _ ] => idtac
      | _ => let Hpossible_data := fresh "Hpossible_terminals_data" in
             let v := constr:(@fold_grammar _ _ _ possible_terminals_aidata G) in
             let lem := lazymatch v with
                        | @fold_grammar ?Char ?T ?fpdata ?aidata ?G
                          => constr:(@Build_fold_grammar_data' Char T fpdata aidata G)
                        end in
             pose (@hide _ lem) as Hlem;
               let compiled_ps := lazymatch v with
                                  | @fold_grammar ?Char ?T ?fpdata ?aidata ?G
                                    => constr:(@opt.compile_grammar _ _ (@compile_item_data_of_abstract_interpretation _ _ fpdata aidata G) G)
                                  end in
               let compiled_ps' := (eval vm_compute in compiled_ps) in
               pose (@hide _ compiled_ps') as Hcompiled_ps;
                 let v := constr:(v compiled_ps') in
                 (*let v' := (eval vm_compute in v) in*)
                 pose v as Hv
      end;
      exfalso.
    Time let fold_grammar_type := lazymatch type of Hlem with
                                  | forall cp Hcp (fg : @?FG cp), _ => FG
                                  end in
         let compiled_ps' := (eval vm_compute in Hcompiled_ps) in
         let lem := (eval cbv [Hlem hide] in Hlem) in
         let v' := (eval vm_compute in Hv) in
         pose v'.
    Set Silent.
    Unset Silent.
    Show. (*
         let k := constr:(lem compiled_ps' ltac:(vm_cast_no_check (eq_refl compiled_ps')) (v' <: fold_grammar_type compiled_ps') ltac:(vm_cast_no_check (eq_refl v'))) in
         idtac.
    Notation prevmcomputed_search_data
      := {| fgd_fold_grammar := _ |}.
    pose (Hlem _ eq_refl _ eq_refl) as Hlemv.
    Time vm_compute in Hlemv.
    let T := type of Hv in
    pose T as HT.
    change HT in (type of Hv).
    Time vm_compute in HT.
    subst HT.
    pose (FMapPositive.PositiveMap.cardinal Hv) as l.

    Time vm_compute in l.
    pose (List.length Hv) as l.
    Time vm_compute in Hv.
    Set Silent.
    Unset Silent.
    cbv [fold_grammar] in Hv.
    Unset Silent.
    cbv [pre_Fix_grammar] in Hv.
    cbv [pre_Fix_grammar_helper] in Hv.
    cbv [aggregate_state fixedpoint_by_abstract_interpretation] in Hv.
    Time vm_compute in

    set (HT := T) in Hv.
    Set Silent.
  constr:((@hide _ lem, @hide _ compiled_ps', @hide _ v'))(*
  let k := constr:(lem compiled_ps' ltac:(vm_cast_no_check (eq_refl compiled_ps')) v' (*ltac:(vm_cast_no_check (eq_refl v'))*))*) in
  v (*
  constr:(lem compiled_ps' ltac:(vm_cast_no_check (eq_refl compiled_ps')) v' ltac:(vm_cast_no_check (eq_refl v'))) in
                        constr:(v : possible_data G)*) in
             pose val as Hpossible_data(*;
               cbv beta in Hpossible_data*)
      end.
    exfalso.
    rename Hpossible_terminals_data into v; clear -v.
    Time vm_compute in v.

    Time start honing parser using indexed representation.
    Show Ltac Profile.

    Reset Ltac Profile.
    Time hone method "splits".
    Show Ltac Profile.
    {
      Reset Ltac Profile.
      Time simplify parser splitter.
      Show Ltac Profile.
      { Time refine_disjoint_search_for. }
      { Time refine_disjoint_search_for. }
      { Time refine_disjoint_search_for. }
      { Time refine_disjoint_search_for. }
      { Time rewrite_disjoint_search_for. }
      { Time rewrite_disjoint_search_for. }
      { Time rewrite_disjoint_rev_search_for. }
      { Time rewrite_disjoint_search_for. }
      { Time refine_binop_table. }
      { Time rewrite_disjoint_search_for. }
      { Time refine_binop_table. }
      { Time rewrite_disjoint_search_for. }
      { Time rewrite_disjoint_search_for. }
      { Time rewrite_disjoint_rev_search_for. }
      { Time rewrite_disjoint_search_for. }
      { Time rewrite_disjoint_search_for. }
      { Time rewrite_disjoint_search_for. }
      { Time rewrite_disjoint_search_for. }
      { Time rewrite_disjoint_search_for. }
      { Time rewrite_disjoint_search_for. }
      { Time rewrite_disjoint_search_for. }
      { Time refine_binop_table. }
      { Time rewrite_disjoint_search_for. }
      { Time refine_binop_table. }
      { Time rewrite_disjoint_search_for. }
      { Time rewrite_disjoint_search_for. }

      simplify parser splitter.
      Show Ltac Profile.
      (*
total time:     84.328s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for -----------   0.0%  39.4%      20    4.268s
─rewrite_disjoint_search_for_no_clear --   0.0%  39.3%      20    4.260s
─rewrite_once_disjoint_search_for ------   0.0%  38.8%      40    4.240s
─rewrite_once_disjoint_search_for_specia  33.6%  38.3%      40    4.212s
─refine_binop_table --------------------   0.0%  37.9%       4    8.036s
─setoid_rewrite_refine_binop_table_idx -  37.0%  37.9%       4    8.032s
─simplify parser splitter --------------   0.0%  18.7%       2   14.980s
─simplify_parser_splitter' -------------   0.0%  18.7%      31   12.444s
─simplify ------------------------------   0.0%  18.7%       2   14.980s
─eapply (refine_opt2_fold_right r_o retv  13.5%  13.5%       1   11.364s
─simplify with monad laws --------------   0.0%   4.4%      30    1.900s
─simplify_with_applied_monad_laws ------   0.0%   4.4%      30    1.900s
─rewrite_disjoint_rev_search_for -------   0.0%   3.9%       2    1.636s
─rewrite_disjoint_rev_search_for_no_clea   0.0%   3.8%       2    1.632s
─rewrite_once_disjoint_rev_search_for --   0.0%   3.8%       4    1.608s
─rewrite_once_disjoint_rev_search_for_sp   3.4%   3.7%       4    1.572s
─specialize (lem' H') ------------------   2.7%   2.7%      44    1.996s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for -----------   0.0%  39.4%      20    4.268s
└rewrite_disjoint_search_for_no_clear --   0.0%  39.3%      20    4.260s
└rewrite_once_disjoint_search_for ------   0.0%  38.8%      40    4.240s
└rewrite_once_disjoint_search_for_specia  33.6%  38.3%      40    4.212s
└specialize (lem' H') ------------------   2.6%   2.6%      40    1.996s
─refine_binop_table --------------------   0.0%  37.9%       4    8.036s
└setoid_rewrite_refine_binop_table_idx -  37.0%  37.9%       4    8.032s
─simplify parser splitter --------------   0.0%  18.7%       2   14.980s
└simplify ------------------------------   0.0%  18.7%       2   14.980s
└simplify_parser_splitter' -------------   0.0%  18.7%      31   12.444s
 ├─eapply (refine_opt2_fold_right r_o re  13.5%  13.5%       1   11.364s
 └─simplify with monad laws ------------   0.0%   4.4%      30    1.900s
  └simplify_with_applied_monad_laws ----   0.0%   4.4%      30    1.900s
─rewrite_disjoint_rev_search_for -------   0.0%   3.9%       2    1.636s
└rewrite_disjoint_rev_search_for_no_clea   0.0%   3.8%       2    1.632s
└rewrite_once_disjoint_rev_search_for --   0.0%   3.8%       4    1.608s
└rewrite_once_disjoint_rev_search_for_sp   3.4%   3.7%       4    1.572s
 *)
      Time finish honing parser method.
    }

    Time finish_Sharpening_SplitterADT.

  Time Defined. (* 85 seconds *)

  Lemma ComputationalSplitter
  : FullySharpened (string_spec json'_grammar string_stringlike).
  Proof.
    Reset Ltac Profile.
    Time make_simplified_splitter ComputationalSplitter'. (* 19 s *)
    Show Ltac Profile.
  Time Defined.

Time End IndexedImpl.

Require Export Fiat.Parsers.ParserFromParserADT.
Require Export Fiat.Parsers.ExtrOcamlParsers.
Export Fiat.Parsers.ExtrOcamlParsers.HideProofs.
Require Export Fiat.Parsers.StringLike.OcamlString.

Definition json_parser (str : Coq.Strings.String.string) : bool.
Proof.
  Reset Ltac Profiling.
  Time make_parser (@ComputationalSplitter(* _ String.string_stringlike _ _*)). (* 75 seconds *)
  Show Ltac Profile.
Time Defined.

(*Definition json_parser_ocaml (str : Ocaml.Ocaml.string) : bool.
Proof.
  Time make_parser (@ComputationalSplitter _ Ocaml.string_stringlike _ _). (* 0.82 s *)
Defined.*)

Print json_parser(*_ocaml*).

Recursive Extraction json_parser(*_ocaml*).
(*
Definition main_json := premain json_parser.
Definition main_json_ocaml := premain_ocaml json_parser_ocaml.

Parameter reference_json_parser : Coq.Strings.String.string -> bool.
Parameter reference_json_parser_ocaml : Ocaml.Ocaml.string -> bool.
Extract Constant reference_json_parser
=> "fun str ->
  let needs_b : bool Pervasives.ref = Pervasives.ref false in
  try
    (List.iter (fun ch ->
       match ch, !needs_b with
       | 'a', false -> needs_b := true; ()
       | 'b', true  -> needs_b := false; ()
       | _, _       -> raise Not_found)
       str;
     if !needs_b then false else true)
  with
   | Not_found -> false".
Extract Constant reference_json_parser_ocaml
=> "fun str ->
  let needs_b : bool Pervasives.ref = Pervasives.ref false in
  try
    (String.iter (fun ch ->
       match ch, !needs_b with
       | 'a', false -> needs_b := true; ()
       | 'b', true  -> needs_b := false; ()
       | _, _       -> raise Not_found)
       str;
     if !needs_b then false else true)
  with
   | Not_found -> false".

Definition main_json_reference := premain reference_json_parser.
Definition main_json_reference_ocaml := premain_ocaml reference_json_parser_ocaml.

(*
(* val needs_b : bool Pervasives.ref;; *)
let needs_b = Pervasives.ref false;;

let chan = match Array.length Sys.argv with
| 0 | 1 -> Pervasives.stdin
| 2 -> let chan = Pervasives.open_in Sys.argv.(1)
       in Pervasives.at_exit (fun () -> Pervasives.close_in chan);
	  chan
| argc -> Pervasives.exit argc;;

(* val line : string;; *)
let line = Pervasives.input_line chan;;

String.iter (fun ch ->
  match ch, !needs_b with
  | 'a', false -> needs_b := true; ()
  | 'b', true  -> needs_b := false; ()
  | _, _       -> Pervasives.exit 1)
  line;;

Pervasives.exit 0;;
*)
(*
Definition test0 := json_parser "".
Definition test1 := json_parser "ab".
Definition str400 := "abababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababab".
Definition test2 := json_parser (str400 ++ str400 ++ str400 ++ str400).

Recursive Extraction test0 test1 test2.
*)
*)
*)

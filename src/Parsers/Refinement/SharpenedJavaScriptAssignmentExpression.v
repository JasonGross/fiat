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
    Time start honing parser using indexed representation.
    Show Ltac Profile.

    Reset Ltac Profile.
    Time hone method "splits".
    Show Ltac Profile.
    {
      Reset Ltac Profile.
      Time simplify parser splitter.
      Typeclasses eauto := debug.
      Time pose (string_stringlike_properties : @StringLikeProperties ascii string_stringlikemin string_stringlike). (* 0.024 *)
      Undo.
      Time pose (ltac:(exact string_stringlike_properties) : @StringLikeProperties ascii string_stringlikemin string_stringlike).
      Undo.
      Time pose (ltac:(typeclasses eauto) : @StringLikeProperties ascii string_stringlikemin string_stringlike).
      Undo.
      (*** HERE *)
      Time pose (_ : @StringLikeProperties ascii string_stringlikemin string_stringlike). (* 1.232 *)
      Time pose (ltac:(typeclasses eauto) : @StringLikeProperties ascii string_stringlikemin string_stringlike).
      Show Ltac Profile.
      { Time refine_disjoint_search_for. }
      { Time refine_disjoint_search_for. }
      { Time refine_disjoint_search_for. }
      { (*idtac;
          let lem := fresh "lem" in
          pose_disjoint_search_for lem.
        Import PossibleTerminalsSets.

          idtac;
  let G := (lazymatch goal with
             | [ |- context[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
               => G
             end) in
  match goal with
  | [ |- context[ParserInterface.split_list_is_complete_idx G ?str ?offset ?len ?idx] ]
    => pose proof (lem idx) as lem';
       do 2 (lazymatch type of lem' with
              | forall a : ?T, _ => idtac; let x := fresh in evar (x : T); specialize (lem' x); subst x
              end);
       let T := match type of lem' with forall a : ?T, _ => T end in
       let H' := fresh in
       assert (H' : T) by solve [ solve_disjoint_side_conditions ];
       specialize (lem' H'); clear H' end. (*
       cbv beta delta [id
                         all_possible_ascii_of_nt all_possible_ascii_of_production
                         possible_first_ascii_of_nt possible_first_ascii_of_production
                         possible_last_ascii_of_nt possible_last_ascii_of_production] in lem';
       do 2 (let x := match type of lem' with
                      | context[characters_set_to_ascii_list ?ls]
                        => constr:(characters_set_to_ascii_list ls)
                      end in
             replace_with_vm_compute_in x lem')

  end. *)
cbv beta iota in *.
  Set Printing Coercions.
  cbv [rproduction_of_string] in *.
  cbv [interp_ritem] in *.
  cbv [interp_RCharExpr] in *.
  cbv [irbeq] in *.
  cbv [pregrammar_idata] in *.
  cbn [javascript_assignment_expression_pregrammar] in *.
  pose (all_possible_ascii_of_nt
          (pregrammar'_of_pregrammar
             javascript_assignment_expression_pregrammar)
          "Expression initial,noIn") as k.
  vm_compute in k. *)
        Time refine_disjoint_search_for_with_alt ltac:(fun _ => shelve). } }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time exfalso; admit; refine_disjoint_search_for_leaving_side_conditions. }
    { Time refine_disjoint_search_for. }
    { (** Refinement rules for disjoint rules *)
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.Refinement.PreTactics.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.StringLike.FirstChar.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.Refinement.DisjointLemmas.
Require Import Fiat.Parsers.Refinement.DisjointRulesCommon.
Require Import Fiat.Parsers.Refinement.PossibleTerminalsSets.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Common.List.DisjointFacts.
Export DisjointLemmas.Exports.
Typeclasses eauto := debug.
Time pose (_ : StringLikeProperties ascii).
(*** HERE *)
 Time idtac;
        let G := match goal with |- context[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] => G end in
        let HSLM := match goal with |- context[@ParserInterface.split_list_is_complete_idx ?Char ?G ?HSLM ?HSL] => HSLM end in
        let HSL := match goal with |- context[@ParserInterface.split_list_is_complete_idx ?Char ?G ?HSLM ?HSL] => HSL end in
        let apdata := get_hyp_of_shape (all_possible_data G) in
        idtac;
          let pdata := get_hyp_of_shape (possible_data G) in
  let lem' := constr:(@refine_disjoint_search_for_idx HSLM HSL _ G apdata pdata) in
pose lem'.

  let lem' := match goal with
              | [ |- context[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
                => constr:(fun idx' nt its => lem' str offset len nt its idx')
              end in
  pose proof lem' as lem.
  pose_disjoint_search_for lem.
 Time refine_disjoint_search_for. }
    Time all:try refine_disjoint_search_for.
    }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_binop_table. }
      { Time refine_disjoint_search_for. }
      { Time refine_binop_table. }
      { Time refine_disjoint_search_for. }
      { Time refine_disjoint_search_for. }
      { Time refine_disjoint_rev_search_for. }
      { Time refine_disjoint_search_for. }
      { Time refine_disjoint_search_for. }
      { Time refine_disjoint_search_for. }
      { Time refine_disjoint_search_for. }
      { Time refine_disjoint_search_for. }
      { Time refine_disjoint_search_for. }
      { Time refine_disjoint_search_for. }
      { Time refine_binop_table. }
      { Time refine_disjoint_search_for. }
      { Time refine_binop_table. }
      { Time refine_disjoint_search_for. }
      { Time refine_disjoint_search_for. }

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

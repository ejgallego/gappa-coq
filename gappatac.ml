(***************************************************)
(* Copyright 2008 Jean-Christophe Filliâtre        *)
(* Copyright 2008-2009 Guillaume Melquiond         *)
(*                                                 *)
(* This file is distributed under the terms of the *)
(* GNU Lesser General Public License Version 2.1   *)
(***************************************************)

open Format
open Util
open Pp
open Term
open Tacmach
open Names
open Coqlib
open Libnames
open Evarutil

let debug = ref false

(* 1. gappa syntax trees and output *)

module Constant = struct

  open Bigint

  type t = { mantissa : bigint; base : int; exp : bigint }

  let create (b, m, e) =
    { mantissa = m; base = b; exp = e }

  let of_int x = 
    { mantissa = x; base = 1; exp = zero }

  let print fmt x = match x.base with
    | 1 -> fprintf fmt "%s" (to_string x.mantissa)
    | 2 -> fprintf fmt "%sb%s" (to_string x.mantissa) (to_string x.exp)
    | 10 -> fprintf fmt "%se%s" (to_string x.mantissa) (to_string x.exp)
    | _ -> assert false

end

type binop = Bminus | Bplus | Bmult | Bdiv

type unop = Usqrt | Uabs | Uopp

type rounding_mode = string

type term =
  | Tconst of Constant.t
  | Tvar of string
  | Tbinop of binop * term * term
  | Tunop of unop * term
  | Tround of rounding_mode * term

type pred =
  | Pin of term * Constant.t * Constant.t

let rec print_term fmt = function
  | Tconst c -> Constant.print fmt c
  | Tvar s -> pp_print_string fmt s
  | Tbinop (op, t1, t2) ->
      let op =
        match op with
          | Bplus -> "+" | Bminus -> "-" | Bmult -> "*" | Bdiv -> "/"
        in
      fprintf fmt "(%a %s %a)" print_term t1 op print_term t2
  | Tunop (Uabs, t) ->
      fprintf fmt "|%a|" print_term t
  | Tunop (Uopp | Usqrt as op, t) ->
      let s =
        match op with
          | Uopp -> "-" | Usqrt -> "sqrt" | _ -> assert false
        in
      fprintf fmt "(%s(%a))" s print_term t
  | Tround (m, t) ->
      fprintf fmt "(%s(%a))" m print_term t

let print_pred fmt = function
  | Pin (t, c1, c2) ->
      fprintf fmt "%a in [%a, %a]"
        print_term t Constant.print c1 Constant.print c2

let temp_file f = if !debug then f else Filename.temp_file f ""
let remove_file f = if not !debug then try Sys.remove f with _ -> ()

exception GappaFailed
exception GappaProofFailed

let call_gappa c_of_s hl p =
  let gappa_in = temp_file "gappa_input" in
  let c = open_out gappa_in in
  let fmt = formatter_of_out_channel c in
  fprintf fmt "@[{ "; 
  List.iter (fun h -> fprintf fmt "%a ->@ " print_pred h) hl;
  fprintf fmt "%a }@]@." print_pred p;
  close_out c;
  let gappa_out = temp_file "gappa_output" in
  let cmd = sprintf "gappa -Bcoq-lambda %s > %s 2> /dev/null" gappa_in gappa_out in
  let out = Sys.command cmd in
  if out <> 0 then raise GappaFailed;
  remove_file gappa_in;
  let cin = open_in gappa_out in
  let nb_hyp = Scanf.sscanf (input_line cin) "(* %d *)" (fun i -> i) in
  let constr = c_of_s (Stream.of_channel cin) in
  close_in cin;
  remove_file gappa_out;
  (constr, nb_hyp)

(* 2. coq -> gappa translation *)

exception NotGappa

let logic_dir = ["Coq"; "Logic"; "Decidable"]
let coq_modules =
  init_modules @ [logic_dir] @ arith_modules @ zarith_base_modules
    @ [["Coq"; "ZArith"; "BinInt"];
       ["Coq"; "Reals"; "Rdefinitions"];
       ["Coq"; "Reals"; "Raxioms";];
       ["Coq"; "Reals"; "Rbasic_fun";];
       ["Coq"; "Reals"; "R_sqrt";];
       ["Coq"; "Reals"; "Rfunctions";];
       ["Gappa"; "Gappa_tactic";];
       ["Gappa"; "Gappa_fixed";];
       ["Gappa"; "Gappa_float";];
       ["Gappa"; "Gappa_round_def";];
       ["Gappa"; "Gappa_pred_bnd";];
       ["Gappa"; "Gappa_definitions";];
  ]

let constant = gen_constant_in_modules "gappa" coq_modules

let coq_refl_equal = lazy (constant "refl_equal")
let coq_Rle = lazy (constant "Rle")
let coq_R = lazy (constant "R")

let coq_convert = lazy (constant "convert")
let coq_reUnknown = lazy (constant "reUnknown")
let coq_reFloat2 = lazy (constant "reFloat2")
let coq_reFloat10 = lazy (constant "reFloat10")
let coq_reInteger = lazy (constant "reInteger")
let coq_reBinary = lazy (constant "reBinary")
let coq_reUnary = lazy (constant "reUnary")
let coq_reRound = lazy (constant "reRound")
let coq_roundDN = lazy (constant "roundDN")
let coq_roundUP = lazy (constant "roundUP")
let coq_roundNE = lazy (constant "roundNE")
let coq_roundZR = lazy (constant "roundZR")
let coq_rounding_fixed = lazy (constant "rounding_fixed")
let coq_rounding_float = lazy (constant "rounding_float")
let coq_boAdd = lazy (constant "boAdd")
let coq_boSub = lazy (constant "boSub")
let coq_boMul = lazy (constant "boMul")
let coq_boDiv = lazy (constant "boDiv")
let coq_uoAbs = lazy (constant "uoAbs")
let coq_uoNeg = lazy (constant "uoNeg")
let coq_uoSqrt = lazy (constant "uoSqrt")
let coq_subset = lazy (constant "subset")
let coq_makepairF = lazy (constant "makepairF")

let coq_bool = lazy (constant "bool")
let coq_true = lazy (constant "true")
let coq_false = lazy (constant "false")

let coq_Z0 = lazy (constant "Z0")
let coq_Zpos = lazy (constant "Zpos")
let coq_Zneg = lazy (constant "Zneg")
let coq_xH = lazy (constant "xH")
let coq_xI = lazy (constant "xI")
let coq_xO = lazy (constant "xO")
let coq_IZR = lazy (constant "IZR")

(* translates a closed Coq term p:positive into a FOL term of type int *)
let rec tr_positive p = match kind_of_term p with
  | Term.Construct _ when p = Lazy.force coq_xH ->
      1
  | Term.App (f, [|a|]) when f = Lazy.force coq_xI ->
      2 * (tr_positive a) + 1
  | Term.App (f, [|a|]) when f = Lazy.force coq_xO ->
      2 * (tr_positive a)
  | Term.Cast (p, _, _) ->
      tr_positive p
  | _ ->
      raise NotGappa

(* translates a closed Coq term t:Z into a term of type int *)
let rec tr_arith_constant t = match kind_of_term t with
  | Term.Construct _ when t = Lazy.force coq_Z0 -> 0
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zpos -> tr_positive a
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zneg -> - (tr_positive a)
  | Term.Cast (t, _, _) -> tr_arith_constant t
  | _ -> raise NotGappa

(* translates a closed Coq term p:positive into a FOL term of type bigint *)
let rec tr_bigpositive p = match kind_of_term p with
  | Term.Construct _ when p = Lazy.force coq_xH -> 
      Bigint.one
  | Term.App (f, [|a|]) when f = Lazy.force coq_xI ->
      Bigint.add_1 (Bigint.mult_2 (tr_bigpositive a))
  | Term.App (f, [|a|]) when f = Lazy.force coq_xO ->
      (Bigint.mult_2 (tr_bigpositive a))
  | Term.Cast (p, _, _) ->
      tr_bigpositive p
  | _ ->
      raise NotGappa

(* translates a closed Coq term t:Z into a term of type bigint *)
let rec tr_arith_bigconstant t = match kind_of_term t with
  | Term.Construct _ when t = Lazy.force coq_Z0 -> Bigint.zero
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zpos -> tr_bigpositive a
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zneg -> 
      Bigint.neg (tr_bigpositive a)
  | Term.Cast (t, _, _) -> tr_arith_bigconstant t
  | _ -> raise NotGappa

let decomp c =
  let c, args = decompose_app c in
  kind_of_term c, args

let tr_bool c = match decompose_app c with
  | c, [] when c = Lazy.force coq_true -> true
  | c, [] when c = Lazy.force coq_false -> false
  | _ -> raise NotGappa

let tr_float b m e =
  (b, tr_arith_bigconstant m, tr_arith_bigconstant e)

let tr_binop c = match decompose_app c with
  | c, [] when c = Lazy.force coq_boAdd -> Bplus
  | c, [] when c = Lazy.force coq_boSub -> Bminus
  | c, [] when c = Lazy.force coq_boMul -> Bmult
  | c, [] when c = Lazy.force coq_boDiv -> Bdiv
  | _ -> assert false

let tr_unop c = match decompose_app c with
  | c, [] when c = Lazy.force coq_uoNeg -> Uopp
  | c, [] when c = Lazy.force coq_uoSqrt -> Usqrt
  | c, [] when c = Lazy.force coq_uoAbs -> Uabs
  | _ -> raise NotGappa

let tr_var c = match decomp c with
  | Var x, [] -> string_of_id x
  | _ -> assert false

let tr_mode c = match decompose_app c with
  | c, [] when c = Lazy.force coq_roundDN -> "dn"
  | c, [] when c = Lazy.force coq_roundNE -> "ne"
  | c, [] when c = Lazy.force coq_roundUP -> "up"
  | c, [] when c = Lazy.force coq_roundZR -> "zr"
  | _ -> raise NotGappa

let tr_rounding_mode c = match decompose_app c with
  | c, [a;b] when c = Lazy.force coq_rounding_fixed ->
      let a = tr_mode a in
      let b = tr_arith_constant b in
      sprintf "fixed<%d,%s>" b a
  | c, [a;p;e] when c = Lazy.force coq_rounding_float ->
      let a = tr_mode a in
      let p = tr_positive p in
      let e = tr_arith_constant e in
      sprintf "float<%d,%d,%s>" p (-e) a
  | _ ->
      raise NotGappa

(* REexpr -> term *)
let rec tr_term c0 =
  let c, args = decompose_app c0 in
  match kind_of_term c, args with
    | _, [a] when c = Lazy.force coq_reUnknown ->
        Tvar (tr_var a)
    | _, [a; b] when c = Lazy.force coq_reFloat2 ->
        Tconst (Constant.create (tr_float 2 a b))
    | _, [a; b] when c = Lazy.force coq_reFloat10 ->
        Tconst (Constant.create (tr_float 10 a b))
    | _, [a] when c = Lazy.force coq_reInteger ->
        Tconst (Constant.create (1, tr_arith_bigconstant a, Bigint.zero))
    | _, [op;a;b] when c = Lazy.force coq_reBinary ->
        Tbinop (tr_binop op, tr_term a, tr_term b)
    | _, [op;a] when c = Lazy.force coq_reUnary ->
        Tunop (tr_unop op, tr_term a)
    | _, [op;a] when c = Lazy.force coq_reRound ->
        Tround (tr_rounding_mode op, tr_term a)
    | _ -> 
        msgnl (str "tr_term: " ++ Printer.pr_constr c0); 
        assert false

let tr_rle c =
  let c, args = decompose_app c in
  match kind_of_term c, args with
    | _, [a;b] when c = Lazy.force coq_Rle ->
        begin match decompose_app a, decompose_app b with
          | (ac, [at]), (bc, [bt]) 
            when ac = Lazy.force coq_convert && bc = Lazy.force coq_convert ->
              at, bt
          | _ ->
              raise NotGappa
        end
    | _ ->
        raise NotGappa

let tr_pred c =
  let c, args = decompose_app c in
  match kind_of_term c, args with
    | _, [a;b] when c = build_coq_and () ->
        begin match tr_rle a, tr_rle b with
          | (c1, t1), (t2, c2) when t1 = t2 ->
              begin match tr_term c1, tr_term c2 with
                | Tconst c1, Tconst c2 ->
                    Pin (tr_term t1, c1, c2)
                | _ ->
                    raise NotGappa
              end
          | _ ->
              raise NotGappa
        end
    | _ ->
        raise NotGappa

let is_R c = match decompose_app c with
  | c, [] when c = Lazy.force coq_R -> true
  | _ -> false

let tr_hyps =
  List.fold_left 
    (fun acc (_,h) -> try tr_pred h :: acc with NotGappa -> acc) []

let no_glob f =
  let dg = Dumpglob.coqdoc_freeze () in
  Dumpglob.pause ();
  let res =
    try f () with e ->
      Dumpglob.continue ();
      Dumpglob.coqdoc_unfreeze dg;
      raise e
    in
  Dumpglob.continue ();
  Dumpglob.coqdoc_unfreeze dg;
  res

let evars_to_vmcast sigma (emap, c) =
  let emap = nf_evars emap in
  let change_exist evar =
    let ty = Reductionops.nf_betaiota emap (Evd.existential_type emap evar) in
    mkCast (mkApp (Lazy.force coq_refl_equal,
      [| Lazy.force coq_bool; Lazy.force coq_true|]), VMcast, ty) in
  let rec replace c =
    match kind_of_term c with
      | Evar ev -> change_exist ev
      | _ -> map_constr replace c in
  replace c

let constr_of_stream gl s =
  no_glob (fun () -> Constrintern.interp_open_constr (project gl) (pf_env gl)
    (Pcoq.Gram.Entry.parse Pcoq.Constr.constr (Pcoq.Gram.parsable s)))

let var_name = function
  | Name id ->
      let s = string_of_id id in
      let s = String.sub s 1 (String.length s - 1) in
      mkVar (id_of_string s)
  | Anonymous -> 
      assert false

let build_proof_term c nb_hyp =
  let bl, _ = decompose_lam c in
  let pf = List.fold_right (fun (x,t) pf -> mkApp (pf, [| var_name x |])) bl c in
  let rec aux n pf =
    if n > 0 then aux (n - 1) (mkApp (pf, [| mk_new_meta () |])) else pf
    in
  aux nb_hyp pf

let gappa_internal gl =
  try
    let c = tr_pred (pf_concl gl) in
    let ((emap, pf), nb_hyp) = call_gappa (constr_of_stream gl) (tr_hyps (pf_hyps_types gl)) c in
    let pf = evars_to_vmcast (project gl) (emap, pf) in
    let pf = build_proof_term pf nb_hyp in
    Tacticals.tclTHEN (Tacmach.refine_no_check pf) Tactics.assumption gl
  with 
    | NotGappa -> error "not a gappa goal"
    | GappaFailed -> error "gappa failed"
    | GappaProofFailed -> error "incorrect gappa proof term"

let gappa_prepare =
  let id = Ident (dummy_loc, id_of_string "gappa_prepare") in
  lazy (Tacinterp.interp (Tacexpr.TacArg (Tacexpr.Reference id)))

let gappa gl =
  Coqlib.check_required_library ["Gappa"; "Gappa_tactic"];
  Tactics.tclABSTRACT None (Tacticals.tclTHEN (Lazy.force gappa_prepare) gappa_internal) gl

let _ =
  Tacinterp.overwriting_add_tactic "Gappa" (fun _ -> gappa);
  Tacinterp.overwriting_add_tactic "Gappa_internal" (fun _ -> gappa_internal)

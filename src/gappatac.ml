(***************************************************)
(* Copyright 2008 Jean-Christophe Filliâtre        *)
(* Copyright 2008-2016 Guillaume Melquiond         *)
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

let global_env = ref Environ.empty_env
let global_evd = ref Evd.empty

let pr_constr = Printer.pr_constr
let existential_type evd ex = Evd.existential_type evd ex

IFDEF COQ84 THEN

let is_global c t =
  match c, kind_of_term t with
  | ConstRef c, Const c' -> eq_constant c c'
  | IndRef i, Ind i' -> eq_ind i i'
  | ConstructRef i, Construct i' -> eq_constructor i i'
  | VarRef id, Var id' -> id = id'
  | _ -> false

let eq_constr = (=)

let interp_open_constr = Constrintern.interp_open_constr

let keep = Tactics.keep
let generalize = Tactics.generalize
let convert_concl_no_check = Tacmach.convert_concl_no_check

let location_table = Lexer.location_table
let restore_location_table = Lexer.restore_location_table

ELSE

open Vars
open Universes
open Globnames

IFDEF COQ85 THEN

open Errors

let generalize = Tactics.generalize
let location_table = Lexer.location_table
let restore_location_table = Lexer.restore_location_table

ELSE

open CErrors

let generalize a = Proofview.V82.of_tactic (Tactics.generalize a)
let location_table () = ()
let restore_location_table () = ()

END

IFDEF COQ87 THEN

open Ltac_plugin
open EConstr

let constr_of_global t = of_constr (constr_of_global t)

let is_global t1 t2 = is_global !global_evd t1 t2

let kind_of_term t = kind !global_evd t

let decompose_app t = decompose_app !global_evd t

let decompose_lam t = decompose_lam !global_evd t

let closed0 t = Vars.closed0 !global_evd t

let eq_constr t1 t2 = eq_constr !global_evd t1 t2

let pr_constr = Printer.pr_econstr

let map_constr f t =
  of_constr (map_constr (fun x -> to_constr !global_evd (f (of_constr x))) (to_constr !global_evd t))

END

let interp_open_constr a b = Constrintern.interp_open_constr b a

let keep a = Proofview.V82.of_tactic (Tactics.keep a)
let convert_concl_no_check a b = Proofview.V82.of_tactic (Tactics.convert_concl_no_check a b)

let anomalylabstrm label = anomaly ~label

let coq_reference t1 t2 =
  let th = lazy (coq_reference t1 t2) in
  fun x -> lazy (Lazy.force th x)

let find_reference t1 t2 =
  let th = lazy (find_reference t1 t2) in
  fun x -> lazy (Lazy.force th x)

let is_global c t = is_global (Lazy.force c) t

let constr_of_global f = constr_of_global (Lazy.force f)

DECLARE PLUGIN "gappatac"

END

let has_izr = IFDEF COQ87 THEN true ELSE false END

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

type atom =
  | Ain of term * Constant.t option * Constant.t option
  | Arel of term * term * Constant.t * Constant.t
  | Aeq of term * term

type pred =
  | Patom of atom
  | Pand of pred * pred
  | Por of pred * pred
  | Pnot of pred

(** {1 Symbols needed by the tactics} *)

let coq_Logic = coq_reference "Gappa" ["Init"; "Logic"]
let coq_False = coq_Logic "False"
let coq_True = coq_Logic "True"
let coq_eq = coq_Logic "eq"
let coq_eq_refl = coq_Logic "eq_refl"
let coq_not = coq_Logic "not"
let coq_and = coq_Logic "and"
let coq_or = coq_Logic "or"

let coq_ref_Datatypes = coq_reference "Gappa" ["Init"; "Datatypes"]
let coq_Some = coq_ref_Datatypes "Some"
let coq_cons = coq_ref_Datatypes "cons"
let coq_nil = coq_ref_Datatypes "nil"
let coq_bool = coq_ref_Datatypes "bool"
let coq_true = coq_ref_Datatypes "true"

let coq_ref_BinNums = coq_reference "Gappa" ["Numbers"; "BinNums"]
let coq_Z0 = coq_ref_BinNums "Z0"
let coq_Zpos = coq_ref_BinNums "Zpos"
let coq_Zneg = coq_ref_BinNums "Zneg"
let coq_xH = coq_ref_BinNums "xH"
let coq_xI = coq_ref_BinNums "xI"
let coq_xO = coq_ref_BinNums "xO"

let coq_ref_Rdefinitions = coq_reference "Gappa" ["Reals"; "Rdefinitions"]
let coq_R = coq_ref_Rdefinitions "R"
let coq_R0 = coq_ref_Rdefinitions "R0"
let coq_R1 = coq_ref_Rdefinitions "R1"
let coq_Rle = coq_ref_Rdefinitions "Rle"
let coq_Rplus = coq_ref_Rdefinitions "Rplus"
let coq_Ropp = coq_ref_Rdefinitions "Ropp"
let coq_Rminus = coq_ref_Rdefinitions "Rminus"
let coq_Rmult = coq_ref_Rdefinitions "Rmult"
let coq_Rinv = coq_ref_Rdefinitions "Rinv"
let coq_Rdiv = coq_ref_Rdefinitions "Rdiv"
IFDEF COQ84 THEN
let coq_IZR = coq_False
ELSE
let coq_IZR = coq_ref_Rdefinitions "IZR"
END
let coq_Rabs = coq_reference "Gappa" ["Reals"; "Rbasic_fun"] "Rabs"
let coq_sqrt = coq_reference "Gappa" ["Reals"; "R_sqrt"] "sqrt"
let coq_powerRZ = coq_reference "Gappa" ["Reals"; "Rfunctions"] "powerRZ"

let coq_radix_val = find_reference "Gappa" ["Flocq"; "Core"; "Fcore_Zaux"] "radix_val"

let coq_ref_Gappa_Private = find_reference "Gappa" ["Gappa"; "Gappa_tactic"; "Gappa_Private"]
let coq_convert_tree = coq_ref_Gappa_Private "convert_tree"
let coq_RTree = coq_ref_Gappa_Private "RTree"
let coq_rtTrue = coq_ref_Gappa_Private "rtTrue"
let coq_rtFalse = coq_ref_Gappa_Private "rtFalse"
let coq_rtAtom = coq_ref_Gappa_Private "rtAtom"
let coq_rtNot = coq_ref_Gappa_Private "rtNot"
let coq_rtAnd = coq_ref_Gappa_Private "rtAnd"
let coq_rtOr = coq_ref_Gappa_Private "rtOr"
let coq_rtImpl = coq_ref_Gappa_Private "rtImpl"
let coq_RAtom = coq_ref_Gappa_Private "RAtom"
let coq_raBound = coq_ref_Gappa_Private "raBound"
let coq_raRel = coq_ref_Gappa_Private "raRel"
let coq_raEq = coq_ref_Gappa_Private "raEq"
let coq_raLe = coq_ref_Gappa_Private "raLe"
let coq_raGeneric = coq_ref_Gappa_Private "raGeneric"
let coq_raFormat = coq_ref_Gappa_Private "raFormat"
let coq_RExpr = coq_ref_Gappa_Private "RExpr"
let coq_reUnknown = coq_ref_Gappa_Private "reUnknown"
let coq_reFloat2 = coq_ref_Gappa_Private "reFloat2"
let coq_reFloat10 = coq_ref_Gappa_Private "reFloat10"
let coq_reBpow2 = coq_ref_Gappa_Private "reBpow2"
let coq_reBpow10 = coq_ref_Gappa_Private "reBpow10"
let coq_rePow2 = coq_ref_Gappa_Private "rePow2"
let coq_rePow10 = coq_ref_Gappa_Private "rePow10"
let coq_reInteger = coq_ref_Gappa_Private "reInteger"
let coq_reBinary = coq_ref_Gappa_Private "reBinary"
let coq_reUnary = coq_ref_Gappa_Private "reUnary"
let coq_reRound = coq_ref_Gappa_Private "reRound"
let coq_mRndDN = coq_ref_Gappa_Private "mRndDN"
let coq_mRndNA = coq_ref_Gappa_Private "mRndNA"
let coq_mRndNE = coq_ref_Gappa_Private "mRndNE"
let coq_mRndUP = coq_ref_Gappa_Private "mRndUP"
let coq_mRndZR = coq_ref_Gappa_Private "mRndZR"
let coq_fFloat = coq_ref_Gappa_Private "fFloat"
let coq_fFloatx = coq_ref_Gappa_Private "fFloatx"
let coq_fFixed = coq_ref_Gappa_Private "fFixed"
let coq_boAdd = coq_ref_Gappa_Private "boAdd"
let coq_boSub = coq_ref_Gappa_Private "boSub"
let coq_boMul = coq_ref_Gappa_Private "boMul"
let coq_boDiv = coq_ref_Gappa_Private "boDiv"
let coq_uoAbs = coq_ref_Gappa_Private "uoAbs"
let coq_uoNeg = coq_ref_Gappa_Private "uoNeg"
let coq_uoInv = coq_ref_Gappa_Private "uoInv"
let coq_uoSqrt = coq_ref_Gappa_Private "uoSqrt"

let coq_ref_Fcore_Raux = find_reference "Gappa" ["Flocq"; "Core"; "Fcore_Raux"]
let coq_bpow = coq_ref_Fcore_Raux "bpow"
let coq_rndDN = coq_ref_Fcore_Raux "Zfloor"
let coq_rndUP = coq_ref_Fcore_Raux "Zceil"
let coq_rndZR = coq_ref_Fcore_Raux "Ztrunc"
let coq_ref_Gappa_round_def = find_reference "Gappa" ["Gappa"; "Gappa_round_def"]
let coq_rndNE = coq_ref_Gappa_round_def "rndNE"
let coq_rndNA = coq_ref_Gappa_round_def "rndNA"
let coq_ref_Fcore_generic_fmt = find_reference "Gappa" ["Flocq"; "Core"; "Fcore_generic_fmt"]
let coq_round = coq_ref_Fcore_generic_fmt "round"
let coq_generic_format = coq_ref_Fcore_generic_fmt "generic_format"
let coq_ref_Fcore_FLT = find_reference "Gappa" ["Flocq"; "Core"; "Fcore_FLT"]
let coq_FLT_format = coq_ref_Fcore_FLT "FLT_format"
let coq_FLT_exp = coq_ref_Fcore_FLT "FLT_exp"
let coq_ref_Fcore_FLX = find_reference "Gappa" ["Flocq"; "Core"; "Fcore_FLX"]
let coq_FLX_format = coq_ref_Fcore_FLX "FLX_format"
let coq_FLX_exp = coq_ref_Fcore_FLX "FLX_exp"
let coq_ref_Fcore_FIX = find_reference "Gappa" ["Flocq"; "Core"; "Fcore_FIX"]
let coq_FIX_format = coq_ref_Fcore_FIX "FIX_format"
let coq_FIX_exp = coq_ref_Fcore_FIX "FIX_exp"

(** {1 Reification from Coq user goal: the [gappa_quote] tactic} *)

exception NotGappa of constr

let var_terms = Hashtbl.create 17
let var_names = Hashtbl.create 17
let var_list = ref []

let mkLApp f v = mkApp (constr_of_global f, v)

let mkList t =
  List.fold_left (fun acc v -> mkLApp coq_cons [|t; v; acc|]) (mkLApp coq_nil [|t|])

let rec mk_pos n =
  if n = 1 then constr_of_global coq_xH
  else if n land 1 = 0 then mkLApp coq_xO [|mk_pos (n / 2)|]
  else mkLApp coq_xI [|mk_pos (n / 2)|]

type int_type = It_1 | It_2 | It_even of constr | It_int of constr | It_none of constr
type int_type_partial = Itp_1 | Itp_2 | Itp_even of int | Itp_int of int

(** translate a closed Coq term [p:positive] into [int] *)
let rec tr_positive p = match kind_of_term p with
  | Term.Construct _ when is_global coq_xH p -> 1
  | Term.App (f, [|a|]) when is_global coq_xI f -> 2 * (tr_positive a) + 1
  | Term.App (f, [|a|]) when is_global coq_xO f -> 2 * (tr_positive a)
  | Term.Cast (p, _, _) -> tr_positive p
  | _ -> raise (NotGappa p)

(** translate a closed Coq term [t:Z] into [int] *)
let rec tr_arith_constant t = match kind_of_term t with
  | Term.Construct _ when is_global coq_Z0 t -> 0
  | Term.App (f, [|a|]) when is_global coq_Zpos f -> tr_positive a
  | Term.App (f, [|a|]) when is_global coq_Zneg f -> - (tr_positive a)
  | Term.Cast (t, _, _) -> tr_arith_constant t
  | _ -> raise (NotGappa t)

(** translate a closed Coq term [t:R] into [int] *)
let tr_real_constant t =
  let rec aux t =
    match decompose_app t with
      | c, [] when is_global coq_R1 c -> Itp_1
      | c, [a] when has_izr && is_global coq_IZR c ->
          Itp_int (tr_arith_constant a)
      | c, [a;b] ->
          if is_global coq_Rplus c then
            if aux a = Itp_1 then
              match aux b with
                | Itp_1 -> Itp_2
                | Itp_2 -> Itp_int 3
                | Itp_even n -> Itp_int (2 * n + 1)
                | _ -> raise (NotGappa t)
            else
              raise (NotGappa t)
          else if is_global coq_Rmult c then
            if aux a = Itp_2 then
              match aux b with
                | Itp_2 -> Itp_even 2
                | Itp_even n -> Itp_even (2 * n)
                | Itp_int n -> Itp_even n
                | _ -> raise (NotGappa t)
            else
              raise (NotGappa t)
          else
            raise (NotGappa t)
      | _ ->
        raise (NotGappa t)
    in
  match aux t with
    | Itp_1 -> 1
    | Itp_2 -> 2
    | Itp_even n -> 2 * n
    | Itp_int n -> n

(** create a term of type [Z] from a quoted real (supposedly constant) *)
let plain_of_int =
  let wrap t =
    mkLApp coq_reInteger [|mkLApp coq_Zpos [|t|]|] in
  function
    | It_1 -> wrap (constr_of_global coq_xH)
    | It_2 -> wrap (mkLApp coq_xO [|constr_of_global coq_xH|])
    | It_even n -> wrap (mkLApp coq_xO [|n|])
    | It_int n -> wrap n
    | It_none n -> n

(** reify a format [Z->Z] *)
let qt_fmt f =
  match decompose_app f with
    | c, [e;p] when is_global coq_FLT_exp c -> mkLApp coq_fFloat [|e;p|]
    | c, [p] when is_global coq_FLX_exp c -> mkLApp coq_fFloatx [|p|]
    | c, [e] when is_global coq_FIX_exp c -> mkLApp coq_fFixed [|e|]
    | _ -> raise (NotGappa f)

(** reify a Coq term [t:R] *)
let rec qt_term t =
  plain_of_int (qt_Rint t)
and qt_Rint t =
  match decompose_app t with
    | c, [] when is_global coq_R1 c -> It_1
    | c, [a;b] ->
        if is_global coq_Rplus c then
          let a = qt_Rint a in
          if a = It_1 then
            match qt_Rint b with
              | It_1 -> It_2
              | It_2 -> It_int (mkLApp coq_xI [|constr_of_global coq_xH|])
              | It_even n -> It_int (mkLApp coq_xI [|n|])
              | (It_int n) as b ->
                  It_none (mkLApp coq_reBinary
                    [|constr_of_global coq_boAdd; plain_of_int a; plain_of_int b|])
              | It_none e ->
                  It_none (mkLApp coq_reBinary
                    [|constr_of_global coq_boAdd; plain_of_int a; e|])
          else
            It_none (mkLApp coq_reBinary
              [|constr_of_global coq_boAdd; plain_of_int a; qt_term b|])
        else if is_global coq_Rmult c then
          let a = qt_Rint a in
          if a = It_2 then
            match qt_Rint b with
              | It_2 -> It_even (mkLApp coq_xO [|constr_of_global coq_xH|])
              | It_even n -> It_even (mkLApp coq_xO [|n|])
              | It_int n -> It_even n
              | _ as b ->
                  It_none (mkLApp coq_reBinary
                    [|constr_of_global coq_boMul; plain_of_int a; plain_of_int b|])
          else
            It_none (mkLApp coq_reBinary
              [|constr_of_global coq_boMul; plain_of_int a; qt_term b|])
        else
          It_none (qt_no_Rint t)
    | _ ->
      It_none (qt_no_Rint t)
and qt_no_Rint t =
  try
    match decompose_app t with
      | c, [] when is_global coq_R0 c ->
        mkLApp coq_reInteger [|constr_of_global coq_Z0|]
      | c, [a] when has_izr && is_global coq_IZR c ->
        mkLApp coq_reInteger [|a|]
      | c, [a] ->
        begin
          let gen_un f = mkLApp coq_reUnary [|constr_of_global f; qt_term a|] in
          if is_global coq_Ropp c then gen_un coq_uoNeg else
          if is_global coq_Rinv c then gen_un coq_uoInv else
          if is_global coq_Rabs c then gen_un coq_uoAbs else
          if is_global coq_sqrt c then gen_un coq_uoSqrt else
          raise (NotGappa t)
        end
      | c, [_;v;w;b] when is_global coq_round c ->
          (* TODO: check radix *)
          let mode = match decompose_app w with
            | c, [] when is_global coq_rndDN c -> coq_mRndDN
            | c, [] when is_global coq_rndNA c -> coq_mRndNA
            | c, [] when is_global coq_rndNE c -> coq_mRndNE
            | c, [] when is_global coq_rndUP c -> coq_mRndUP
            | c, [] when is_global coq_rndZR c -> coq_mRndZR
            | _ -> raise (NotGappa w) in
          mkLApp coq_reRound [|qt_fmt v; constr_of_global mode; qt_term b|]
      | c, [a;b] ->
          let gen_bin f = mkLApp coq_reBinary [|constr_of_global f; qt_term a; qt_term b|] in
          if is_global coq_Rminus c then gen_bin coq_boSub else
          if is_global coq_Rdiv c then gen_bin coq_boDiv else
          if is_global coq_powerRZ c then
            let p =
              match tr_real_constant a with
                | 2 -> coq_rePow2
                | 10 -> coq_rePow10
                | _ -> raise (NotGappa t)
              in
            mkLApp p [|(ignore (tr_arith_constant b); b)|] else
          if is_global coq_bpow c then
            let p =
              match tr_arith_constant
                      (Tacred.compute !global_env !global_evd
                                      (mkLApp coq_radix_val [|a|])) with
                | 2 -> coq_reBpow2
                | 10 -> coq_reBpow10
                | _ -> raise (NotGappa t)
              in
            mkLApp p [|(ignore (tr_arith_constant b); b)|]
          else raise (NotGappa t)
      | _ -> raise (NotGappa t)
  with NotGappa _ ->
    try
      Hashtbl.find var_terms t
    with Not_found ->
      let e = mkLApp coq_reUnknown [|mk_pos (Hashtbl.length var_terms + 1)|] in
      Hashtbl.add var_terms t e;
      var_list := t :: !var_list;
      e

(** reify a Coq term [p:Prop] *)
let rec qt_pred p = match kind_of_term p with
  | Prod (_,a,b) ->
    if not (closed0 b) then raise (NotGappa p);
    mkLApp coq_rtImpl [|qt_pred a; qt_pred b|]
  | _ ->
match decompose_app p with
  | c, [] when is_global coq_True c ->
      constr_of_global coq_rtTrue
  | c, [] when is_global coq_False c ->
      constr_of_global coq_rtFalse
  | c, [a] when is_global coq_not c ->
      mkLApp coq_rtNot [|qt_pred a|]
  | c, [a;b] when is_global coq_and c ->
      begin match decompose_app a, decompose_app b with
        | (c1, [a1;b1]), (c2, [a2;b2])
          when is_global coq_Rle c1 && is_global coq_Rle c2 && eq_constr b1 a2 ->
            mkLApp coq_rtAtom [|mkLApp coq_raBound
              [|mkLApp coq_Some [|constr_of_global coq_RExpr; qt_term a1|]; qt_term b1;
                mkLApp coq_Some [|constr_of_global coq_RExpr; qt_term b2|]|]|]
        | _ ->
            mkLApp coq_rtAnd [|qt_pred a; qt_pred b|]
      end
  | c, [a;b] when is_global coq_or c ->
      mkLApp coq_rtOr [|qt_pred a; qt_pred b|]
  | c, [a;b] when is_global coq_Rle c ->
      mkLApp coq_rtAtom [|mkLApp coq_raLe [|qt_term a; qt_term b|]|]
  | c, [t;a;b] when is_global coq_eq c && is_global coq_R t ->
      mkLApp coq_rtAtom [|mkLApp coq_raEq [|qt_term a; qt_term b|]|]
  | c, [_;e;x] when is_global coq_FIX_format c ->
      let fmt = mkLApp coq_fFixed [|e|] in
      mkLApp coq_rtAtom [|mkLApp coq_raFormat [|fmt; qt_term x|]|]
  | c, [_;e;p;x] when is_global coq_FLT_format c ->
      let fmt = mkLApp coq_fFloat [|e;p|] in
      mkLApp coq_rtAtom [|mkLApp coq_raFormat [|fmt; qt_term x|]|]
  | c, [_;p;x] when is_global coq_FLX_format c ->
      let fmt = mkLApp coq_fFloatx [|p|] in
      mkLApp coq_rtAtom [|mkLApp coq_raFormat [|fmt; qt_term x|]|]
  | c, [_;f;x] when is_global coq_generic_format c ->
      mkLApp coq_rtAtom [|mkLApp coq_raGeneric [|qt_fmt f; qt_term x|]|]
  | _ -> raise (NotGappa p)

(** reify hypotheses *)
let qt_hyps =
  List.fold_left (fun acc (n, h) ->
    let old_var_list = !var_list in
    try (n, qt_pred h) :: acc
    with NotGappa _ ->
      while not (!var_list == old_var_list) do
        match !var_list with
        | h :: q ->
          Hashtbl.remove var_terms h;
          var_list := q
        | [] -> assert false
      done;
      acc) []

(** the [gappa_quote] tactic *)
let gappa_quote gl =
  try
    global_env := pf_env gl;
    global_evd := project gl;
    let l = qt_hyps (pf_hyps_types gl) in
    let _R = constr_of_global coq_R in
    let g = List.fold_left
      (fun acc (_, h) -> mkLApp coq_rtImpl [|h; acc|])
      (qt_pred (pf_concl gl)) l in
    let uv = mkList _R !var_list in
    let e = mkLApp coq_convert_tree [|uv; g|] in
    (*Pp.msgerrnl (pr_constr e);*)
    Hashtbl.clear var_terms;
    var_list := [];
    Tacticals.tclTHEN
      (Tacticals.tclTHEN
        (generalize (List.map (fun (n, _) -> mkVar n) (List.rev l)))
        (keep []))
      (convert_concl_no_check e DEFAULTcast) gl
  with
    | NotGappa t ->
      Hashtbl.clear var_terms;
      var_list := [];
      anomalylabstrm "gappa_quote"
        (Pp.str "something wrong happened with term " ++ pr_constr t)

(** {1 Goal parsing, call to Gappa, and proof building: the [gappa_internal] tactic} *)

(** translate a closed Coq term [p:positive] into [bigint] *)
let rec tr_bigpositive p = match kind_of_term p with
  | Term.Construct _ when is_global coq_xH p ->
      Bigint.one
  | Term.App (f, [|a|]) when is_global coq_xI f ->
      Bigint.add_1 (Bigint.mult_2 (tr_bigpositive a))
  | Term.App (f, [|a|]) when is_global coq_xO f ->
      (Bigint.mult_2 (tr_bigpositive a))
  | Term.Cast (p, _, _) ->
      tr_bigpositive p
  | _ ->
      raise (NotGappa p)

(** translate a closed Coq term [t:Z] into [bigint] *)
let rec tr_arith_bigconstant t = match kind_of_term t with
  | Term.Construct _ when is_global coq_Z0 t -> Bigint.zero
  | Term.App (f, [|a|]) when is_global coq_Zpos f -> tr_bigpositive a
  | Term.App (f, [|a|]) when is_global coq_Zneg f ->
      Bigint.neg (tr_bigpositive a)
  | Term.Cast (t, _, _) -> tr_arith_bigconstant t
  | _ -> raise (NotGappa t)

let tr_float b m e =
  (b, tr_arith_bigconstant m, tr_arith_bigconstant e)

let tr_binop c = match decompose_app c with
  | c, [] when is_global coq_boAdd c -> Bplus
  | c, [] when is_global coq_boSub c -> Bminus
  | c, [] when is_global coq_boMul c -> Bmult
  | c, [] when is_global coq_boDiv c -> Bdiv
  | _ -> assert false

let tr_unop c = match decompose_app c with
  | c, [] when is_global coq_uoNeg c -> Uopp
  | c, [] when is_global coq_uoSqrt c -> Usqrt
  | c, [] when is_global coq_uoAbs c -> Uabs
  | _ -> raise (NotGappa c)

(** translate a Coq term [c:RExpr] into [term] *)
let rec tr_term uv t =
  match decompose_app t with
    | c, [a] when is_global coq_reUnknown c ->
        let n = tr_positive a - 1 in
        if (n < Array.length uv) then Tvar uv.(n)
        else raise (NotGappa t)
    | c, [a; b] when is_global coq_reFloat2 c ->
        Tconst (Constant.create (tr_float 2 a b))
    | c, [a; b] when is_global coq_reFloat10 c ->
        Tconst (Constant.create (tr_float 10 a b))
    | c, [a] when is_global coq_reInteger c ->
        Tconst (Constant.create (1, tr_arith_bigconstant a, Bigint.zero))
    | c, [op;a;b] when is_global coq_reBinary c ->
        Tbinop (tr_binop op, tr_term uv a, tr_term uv b)
    | c, [op;a] when is_global coq_reUnary c ->
        Tunop (tr_unop op, tr_term uv a)
    | c, [fmt;mode;a] when is_global coq_reRound c ->
        let mode = match decompose_app mode with
          | c, [] when is_global coq_mRndDN c -> "dn"
          | c, [] when is_global coq_mRndNA c -> "na"
          | c, [] when is_global coq_mRndNE c -> "ne"
          | c, [] when is_global coq_mRndUP c -> "up"
          | c, [] when is_global coq_mRndZR c -> "zr"
          | _ -> raise (NotGappa mode) in
        let rnd = match decompose_app fmt with
          | c, [e;p] when is_global coq_fFloat c ->
              let e = tr_arith_constant e in
              let p = tr_arith_constant p in
              sprintf "float<%d,%d,%s>" p e mode
          | c, [p] when is_global coq_fFloatx c ->
              let p = tr_arith_constant p in
              sprintf "float<%d,%s>" p mode
          | c, [e] when is_global coq_fFixed c ->
              let e = tr_arith_constant e in
              sprintf "fixed<%d,%s>" e mode
          | _ -> raise (NotGappa fmt) in
        Tround (rnd, tr_term uv a)
    | _ ->
        raise (NotGappa t)

let tr_const c =
  match tr_term [||] c with
    | Tconst v -> v
    | _ -> raise (NotGappa c)

(** translate a Coq term [t:RAtom] into [pred] *)
let tr_atom uv t =
  match decompose_app t with
    | c, [l;e;u] when is_global coq_raBound c ->
        let l = match decompose_app l with
          | (_, [_;l]) -> Some (tr_const l)
          | (_, [_]) -> None
          | _ -> assert false in
        let u = match decompose_app u with
          | (_, [_;u]) -> Some (tr_const u)
          | (_, [_]) -> None
          | _ -> assert false in
        if l = None && u = None then raise (NotGappa t);
        Ain (tr_term uv e, l, u)
    | c, [er;ex;l;u] when is_global coq_raRel c ->
        Arel (tr_term uv er, tr_term uv ex, tr_const l, tr_const u)
    | c, [er;ex] when is_global coq_raEq c ->
        Aeq (tr_term uv er, tr_term uv ex)
    | _ ->
        raise (NotGappa t)

(** translate a Coq term [t:RTree] into [pred] *)
let rec tr_pred uv t =
  match decompose_app t with
    | c, [a] when is_global coq_rtAtom c ->
        Patom (tr_atom uv a)
    | c, [a] when is_global coq_rtNot c ->
        Pnot (tr_pred uv a)
    | c, [a;b] when is_global coq_rtAnd c ->
        Pand (tr_pred uv a, tr_pred uv b)
    | c, [a;b] when is_global coq_rtOr c ->
        Por (tr_pred uv a, tr_pred uv b)
    | _ ->
        raise (NotGappa t)

let tr_var c = match kind_of_term c with
  | Var x ->
    let s = String.copy (string_of_id x) in
    for i = 0 to String.length s - 1 do
      let c = s.[i] in
      if not (('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z') ||
        ('0' <= c && c <= '9') || c == '_') then s.[i] <- '_';
    done;
    if s.[0] = '_' then s.[0] <- 'G';
    let s = ref s in
    begin try
      while true do
        ignore (Hashtbl.find var_names !s);
        s := !s ^ "_";
      done;
      assert false
    with Not_found ->
      Hashtbl.add var_names !s c;
      !s
    end
  | _ -> raise (NotGappa c)

(** translate a Coq term [t:list] into [list] by applying [f] to each element *)
let tr_list f =
  let rec aux c =
    match decompose_app c with
      | _, [_;h;t] -> f h :: aux t
      | _, [_] -> []
      | _ -> raise (NotGappa c)
    in
  aux

(** translate a Coq term [c] of kind [convert_tree ...] *)
let tr_goal c =
  match decompose_app c with
    | c, [uv;e] when is_global coq_convert_tree c ->
        let uv = Array.of_list (tr_list tr_var uv) in
        tr_pred uv e
    | _ -> raise (NotGappa c)

(** print a Gappa term *)
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

(** print a Gappa predicate *)
let print_atom fmt = function
  | Ain (t, Some c1, Some c2) ->
      fprintf fmt "%a in [%a, %a]"
        print_term t Constant.print c1 Constant.print c2
  | Ain (t, Some c, None) ->
      fprintf fmt "%a >= %a" print_term t Constant.print c
  | Ain (t, None, Some c) ->
      fprintf fmt "%a <= %a" print_term t Constant.print c
  | Ain (_, None, None) -> assert false
  | Arel (t1, t2, c1, c2) ->
      fprintf fmt "%a -/ %a in [%a,%a]"
        print_term t1 print_term t2 Constant.print c1 Constant.print c2
  | Aeq (t1, t2) ->
      fprintf fmt "%a = %a" print_term t1 print_term t2

let rec print_pred fmt = function
  | Patom a -> print_atom fmt a
  | Pnot t -> fprintf fmt "not (%a)" print_pred t
  | Pand (t1, t2) -> fprintf fmt "(%a) /\\ (%a)" print_pred t1 print_pred t2
  | Por (t1, t2) -> fprintf fmt "(%a) \\/ (%a)" print_pred t1 print_pred t2

let temp_file f = if !debug then f else Filename.temp_file f ""
let remove_file f = if not !debug then try Sys.remove f with _ -> ()

exception GappaFailed of string

(** print a Gappa goal from [p] and call Gappa on it,
    build a Coq term by calling [c_of_s] *)
let call_gappa c_of_s p =
  let gappa_in = temp_file "gappa_inp" in
  let c = open_out gappa_in in
  let fmt = formatter_of_out_channel c in
  fprintf fmt "@[{ %a }@]@." print_pred p;
  close_out c;
  let gappa_out = temp_file "gappa_out" in
  let gappa_err = temp_file "gappa_err" in
  let cmd = sprintf "gappa -Bcoq-lambda %s > %s 2> %s" gappa_in gappa_out gappa_err in
  let out = Sys.command cmd in
  if out <> 0 then begin
    let c = open_in_bin gappa_err in
    let len = in_channel_length c in
    let buf = String.create len in
    ignore (input c buf 0 len);
    close_in c;
    raise (GappaFailed buf)
  end;
  remove_file gappa_err;
  let cin = open_in gappa_out in
  let constr = c_of_s (Stream.of_channel cin) in
  close_in cin;
  remove_file gappa_in;
  remove_file gappa_out;
  constr

(** execute [f] after disabling globalization *)
let no_glob f =
  let dg = location_table () in
  Dumpglob.pause ();
  let res =
    try f () with e ->
      Dumpglob.continue ();
      restore_location_table dg;
      raise e
    in
  Dumpglob.continue ();
  restore_location_table dg;
  res

(** replace all evars of any type [ty] by [(refl_equal true : ty)] *)
let evars_to_vmcast sigma (emap, c) =
  let emap = nf_evar_map emap in
  let change_exist evar =
    let ty = Reductionops.nf_betaiota emap (existential_type emap evar) in
    mkCast (mkLApp coq_eq_refl
      [|constr_of_global coq_bool; constr_of_global coq_true|], VMcast, ty) in
  let rec replace c =
    match kind_of_term c with
      | Evar ev -> change_exist ev
      | _ -> map_constr replace c
    in
  replace c

let constr_of_stream s =
  no_glob (fun () -> interp_open_constr !global_evd !global_env
    (Pcoq.Gram.entry_parse Pcoq.Constr.constr (Pcoq.Gram.parsable s)))

let var_name = function
  | Name id ->
      let s = string_of_id id in
      let s = String.sub s 1 (String.length s - 1) in
      Hashtbl.find var_names s
  | Anonymous ->
      assert false

(** apply to the proof term [c] all the needed variables from the context
    and as many metas as needed to match hypotheses *)
let build_proof_term c =
  let bl, _ = decompose_lam c in
  List.fold_right (fun (x,t) pf -> mkApp (pf, [| var_name x |])) bl c

(** the [gappa_internal] tactic *)
let gappa_internal gl =
  try
    global_env := pf_env gl;
    global_evd := project gl;
    Hashtbl.clear var_names;
    List.iter (let dummy = mkVar (id_of_string "dummy") in
      fun n -> Hashtbl.add var_names n dummy)
      ["fma"; "sqrt"; "not"; "in"; "float"; "fixed"; "int";
       "homogen80x"; "homogen80x_init"; "float80x";
       "add_rel"; "sub_rel"; "mul_rel"; "fma_rel" ];
    let g = tr_goal (pf_concl gl) in
    let (emap, pf) = call_gappa constr_of_stream g in
    global_evd := emap;
    let pf = evars_to_vmcast emap (emap, pf) in
    let pf = build_proof_term pf in
    Tacmach.refine_no_check pf gl
  with
    | NotGappa t ->
      errorlabstrm "gappa_internal"
        (Pp.str "translation to Gappa failed (not a reduced constant?): " ++ pr_constr t)
    | GappaFailed s ->
      errorlabstrm "gappa_internal"
        (Pp.str "execution of Gappa failed:" ++ Pp.fnl () ++ Pp.str s)

IFDEF COQ84 THEN

ELSE

let gappa_quote = Proofview.V82.tactic gappa_quote
let gappa_internal = Proofview.V82.tactic gappa_internal

END

TACTIC EXTEND gappatac_gappa_internal
| [ "gappa_internal" ] -> [ gappa_internal ]
END

TACTIC EXTEND gappatac_gappa_quote
| [ "gappa_quote" ] -> [ gappa_quote ]
END

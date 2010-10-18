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
  | Prel of term * term * Constant.t * Constant.t

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
  | Prel (t1, t2, c1, c2) ->
      fprintf fmt "%a -/ %a in [%a,%a]"
        print_term t1 print_term t2 Constant.print c1 Constant.print c2

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
  let format = Scanf.sscanf (input_line cin) "(* %d%s *)"
    (fun i s -> (i, s = ",contradiction")) in
  let constr = c_of_s (Stream.of_channel cin) in
  close_in cin;
  remove_file gappa_out;
  (constr, format)

(* 2. coq -> gappa translation *)

exception NotGappa

let logic_dir = ["Coq"; "Logic"; "Decidable"]
let coq_modules =
  init_modules @ [logic_dir] @ arith_modules @ zarith_base_modules
    @ [["Coq"; "ZArith"; "BinInt"];
       ["Coq"; "Reals"; "Rdefinitions"];
       ["Coq"; "Reals"; "Raxioms"];
       ["Coq"; "Reals"; "Rbasic_fun"];
       ["Coq"; "Reals"; "R_sqrt"];
       ["Coq"; "Reals"; "Rfunctions"];
       ["Coq"; "Lists"; "List"];
       ["Gappa"; "Gappa_tactic"];
       ["Gappa"; "Gappa_fixed"];
       ["Gappa"; "Gappa_float"];
       ["Gappa"; "Gappa_round_def"];
       ["Gappa"; "Gappa_pred_bnd"];
       ["Gappa"; "Gappa_definitions"];
       ["Flocq"; "Core"; "Fcore_generic_fmt"];
       ["Flocq"; "Core"; "Fcore_rnd_ne"];
       ["Flocq"; "Core"; "Fcore_FLT"];
       ["Flocq"; "Core"; "Fcore_FIX"];
  ]

let constant = gen_constant_in_modules "gappa" coq_modules

let coq_False = lazy (constant "False")
let coq_eq = lazy (constant "eq")
let coq_refl_equal = lazy (constant "refl_equal")

let coq_and = lazy (constant "and")

let coq_R = lazy (constant "R")
let coq_R0 = lazy (constant "R0")
let coq_R1 = lazy (constant "R1")
let coq_Rle = lazy (constant "Rle")
let coq_Rge = lazy (constant "Rge")

let coq_Rplus = lazy (constant "Rplus")
let coq_Rminus = lazy (constant "Rminus")
let coq_Ropp = lazy (constant "Ropp")
let coq_Rmult = lazy (constant "Rmult")
let coq_Rdiv = lazy (constant "Rdiv")
let coq_Rinv = lazy (constant "Rinv")
let coq_Rabs = lazy (constant "Rabs")
let coq_sqrt = lazy (constant "sqrt")
let coq_powerRZ = lazy (constant "powerRZ")

let coq_Some = lazy (constant "Some")

let coq_pair = lazy (constant "pair")

let coq_list = lazy (constant "list")
let coq_cons = lazy (constant "cons")
let coq_nil = lazy (constant "nil")

let coq_convert_goal = lazy (constant "convert_goal")
let coq_contradict_goal = lazy (constant "contradict_goal")

let coq_RAtom = lazy (constant "RAtom")
let coq_raBound = lazy (constant "raBound")
let coq_raRel = lazy (constant "raRel")
let coq_raEq = lazy (constant "raEq")
let coq_raLe = lazy (constant "raLe")
let coq_raFalse = lazy (constant "raFalse")

let coq_RExpr = lazy (constant "RExpr")
let coq_reUnknown = lazy (constant "reUnknown")
let coq_reFloat2 = lazy (constant "reFloat2")
let coq_reFloat10 = lazy (constant "reFloat10")
let coq_rePow2 = lazy (constant "rePow2")
let coq_rePow10 = lazy (constant "rePow10")
let coq_reInteger = lazy (constant "reInteger")
let coq_reBinary = lazy (constant "reBinary")
let coq_reUnary = lazy (constant "reUnary")
let coq_reApply = lazy (constant "reApply")

let coq_rndDN = lazy (constant "rndDN")
let coq_rndUP = lazy (constant "rndUP")
let coq_rndNE = lazy (constant "rndNE")
let coq_rndZR = lazy (constant "rndZR")
let coq_round = lazy (constant "round")
let coq_FLT_exp = lazy (constant "FLT_exp")
let coq_FIX_exp = lazy (constant "FIX_exp")

let coq_boAdd = lazy (constant "boAdd")
let coq_boSub = lazy (constant "boSub")
let coq_boMul = lazy (constant "boMul")
let coq_boDiv = lazy (constant "boDiv")
let coq_uoAbs = lazy (constant "uoAbs")
let coq_uoNeg = lazy (constant "uoNeg")
let coq_uoInv = lazy (constant "uoInv")
let coq_uoSqrt = lazy (constant "uoSqrt")

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

let var_table = Hashtbl.create 17
let fun_table = Hashtbl.create 17
let var_list = ref []
let fun_list = ref []

let mkLApp f v = mkApp (Lazy.force f, v)

let rec mk_pos n =
  if n = 1 then Lazy.force coq_xH
  else if n land 1 = 0 then mkLApp coq_xO [|mk_pos (n / 2)|]
  else mkLApp coq_xI [|mk_pos (n / 2)|]

type int_type = It_1 | It_2 | It_even of constr | It_int of constr | It_none of constr
type int_type_partial = Itp_1 | Itp_2 | Itp_even of int | Itp_int of int

(* translates a closed Coq term p:positive into an int *)
let rec tr_positive p = match kind_of_term p with
  | Term.Construct _ when p = Lazy.force coq_xH -> 1
  | Term.App (f, [|a|]) when f = Lazy.force coq_xI -> 2 * (tr_positive a) + 1
  | Term.App (f, [|a|]) when f = Lazy.force coq_xO -> 2 * (tr_positive a)
  | Term.Cast (p, _, _) -> tr_positive p
  | _ ->
      raise NotGappa

(* translates a closed Coq term t:Z into an int *)
let rec tr_arith_constant t = match kind_of_term t with
  | Term.Construct _ when t = Lazy.force coq_Z0 -> 0
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zpos -> tr_positive a
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zneg -> - (tr_positive a)
  | Term.Cast (t, _, _) -> tr_arith_constant t
  | _ -> raise NotGappa

(* translates a closed Coq term t:R into an int *)
let tr_real_constant t =
  let rec aux t =
    match decompose_app t with
      | c, [] when c = Lazy.force coq_R1 -> Itp_1
      | c, [a;b] ->
          if c = Lazy.force coq_Rplus then
            if aux a = Itp_1 then
              match aux b with
                | Itp_1 -> Itp_2
                | Itp_2 -> Itp_int 3
                | Itp_even n -> Itp_int (2 * n + 1)
                | _ -> raise NotGappa
            else
              raise NotGappa
          else if c = Lazy.force coq_Rmult then
            if aux a = Itp_2 then
              match aux b with
                | Itp_2 -> Itp_even 2
                | Itp_even n -> Itp_even (2 * n)
                | Itp_int n -> Itp_even n
                | _ -> raise NotGappa
            else
              raise NotGappa
          else
            raise NotGappa
      | _ ->
        raise NotGappa
    in
  match aux t with
    | Itp_1 -> 1
    | Itp_2 -> 2
    | Itp_even n -> 2 * n
    | Itp_int n -> n

let plain_of_int =
  let wrap t =
    mkLApp coq_reInteger [|mkLApp coq_Zpos [|t|]|] in
  function
    | It_1 -> wrap (Lazy.force coq_xH)
    | It_2 -> wrap (mkLApp coq_xO [|Lazy.force coq_xH|])
    | It_even n -> wrap (mkLApp coq_xO [|n|])
    | It_int n -> wrap n
    | It_none n -> n

let qt_round qt_a qt_b =
  let n =
    try
      Hashtbl.find fun_table qt_a
    with Not_found ->
      let n = mk_pos (Hashtbl.length fun_table + 1) in
      Hashtbl.replace fun_table qt_a n;
      fun_list := qt_a :: !fun_list;
      n
    in
  mkLApp coq_reApply [|n; qt_b|]

let rec qt_Rint t =
  match decompose_app t with
    | c, [] when c = Lazy.force coq_R1 -> It_1
    | c, [a;b] ->
        if c = Lazy.force coq_Rplus then
          let a = qt_Rint a in
          if a = It_1 then
            match qt_Rint b with
              | It_1 -> It_2
              | It_2 -> It_int (mkLApp coq_xI [|Lazy.force coq_xH|])
              | It_even n -> It_int (mkLApp coq_xI [|n|])
              | (It_int n) as b ->
                  It_none (mkLApp coq_reBinary
                    [|Lazy.force coq_boAdd; plain_of_int a; plain_of_int b|])
              | It_none e ->
                  It_none (mkLApp coq_reBinary
                    [|Lazy.force coq_boAdd; plain_of_int a; e|])
          else
            It_none (mkLApp coq_reBinary
              [|Lazy.force coq_boAdd; plain_of_int a; qt_term b|])
        else if c = Lazy.force coq_Rmult then
          let a = qt_Rint a in
          if a = It_2 then
            match qt_Rint b with
              | It_2 -> It_even (mkLApp coq_xO [|Lazy.force coq_xH|])
              | It_even n -> It_even (mkLApp coq_xO [|n|])
              | It_int n -> It_even n
              | _ as b ->
                  It_none (mkLApp coq_reBinary
                    [|Lazy.force coq_boMul; plain_of_int a; plain_of_int b|])
          else
            It_none (mkLApp coq_reBinary
              [|Lazy.force coq_boMul; plain_of_int a; qt_term b|])
        else
          It_none (qt_no_Rint t)
    | _ ->
      It_none (qt_no_Rint t)
and qt_no_Rint t =
  try
    match decompose_app t with
      | c, [] when c = Lazy.force coq_R0 ->
        mkLApp coq_reInteger [|Lazy.force coq_Z0|]
      | c, [a] ->
        begin
          let gen_un f = mkLApp coq_reUnary [|Lazy.force f; qt_term a|] in
          if c = Lazy.force coq_Ropp then gen_un coq_uoNeg else
          if c = Lazy.force coq_Rinv then gen_un coq_uoInv else
          if c = Lazy.force coq_Rabs then gen_un coq_uoAbs else
          if c = Lazy.force coq_sqrt then gen_un coq_uoSqrt else
          try
            let n = Hashtbl.find fun_table c in
            mkLApp coq_reApply [|n; qt_term a|]
          with Not_found ->
            raise NotGappa
        end
      | c, [u;v;w;b] when c = Lazy.force coq_round ->
          qt_round (mkLApp coq_round [|u;v;w|]) (qt_term b)
      | c, [a;b] ->
          let gen_bin f = mkLApp coq_reBinary [|Lazy.force f; qt_term a; qt_term b|] in
          if c = Lazy.force coq_Rminus then gen_bin coq_boSub else
          if c = Lazy.force coq_Rdiv then gen_bin coq_boDiv else
          if c = Lazy.force coq_powerRZ then
            let p =
              match tr_real_constant a with
                | 2 -> coq_rePow2
                | 10 -> coq_rePow10
                | _ -> raise NotGappa
              in
            mkLApp p [|(ignore (tr_arith_constant b); b)|]
          else raise NotGappa
      | _ -> raise NotGappa
  with NotGappa ->
    try
      Hashtbl.find var_table t
    with Not_found ->
      let e = mkLApp coq_reUnknown [|mk_pos (Hashtbl.length var_table + 1)|] in
      Hashtbl.replace var_table t e;
      var_list := t :: !var_list;
      e
and qt_term t =
  plain_of_int (qt_Rint t)

let qt_pred p = match decompose_app p with
  | c, [a;b] when c = Lazy.force coq_and ->
      begin match decompose_app a, decompose_app b with
        | (c1, [a1;b1]), (c2, [a2;b2])
          when c1 = Lazy.force coq_Rle && c2 = Lazy.force coq_Rle && b1 = a2 ->
            mkLApp coq_raBound
              [|mkLApp coq_Some [|Lazy.force coq_RExpr; qt_term a1|]; qt_term b1;
                mkLApp coq_Some [|Lazy.force coq_RExpr; qt_term b2|]|]
        | _ ->
            raise NotGappa
      end
  | c, [a;b] when c = Lazy.force coq_Rle ->
      mkLApp coq_raLe [|qt_term a; qt_term b|]
  | c, [a;b] when c = Lazy.force coq_Rge ->
      mkLApp coq_raLe [|qt_term b; qt_term a|]
  | c, [t;a;b] when c = Lazy.force coq_eq && t = Lazy.force coq_R ->
      mkLApp coq_raEq [|qt_term a; qt_term b|]
  | _ -> raise NotGappa

let qt_hyps =
  List.fold_left
    (fun acc (n, h) -> try (n, qt_pred h) :: acc with NotGappa -> acc) []

(* translates a closed Coq term p:positive into a bigint *)
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

(* translates a closed Coq term t:Z into a bigint *)
let rec tr_arith_bigconstant t = match kind_of_term t with
  | Term.Construct _ when t = Lazy.force coq_Z0 -> Bigint.zero
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zpos -> tr_bigpositive a
  | Term.App (f, [|a|]) when f = Lazy.force coq_Zneg ->
      Bigint.neg (tr_bigpositive a)
  | Term.Cast (t, _, _) -> tr_arith_bigconstant t
  | _ -> raise NotGappa

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

(* RExpr -> term *)
let rec tr_term uv uf c =
  match decompose_app c with
    | c, [a] when c = Lazy.force coq_reUnknown ->
        let n = tr_positive a - 1 in
        if (n < Array.length uv) then Tvar uv.(n)
        else raise NotGappa
    | c, [a; b] when c = Lazy.force coq_reFloat2 ->
        Tconst (Constant.create (tr_float 2 a b))
    | c, [a; b] when c = Lazy.force coq_reFloat10 ->
        Tconst (Constant.create (tr_float 10 a b))
    | c, [a] when c = Lazy.force coq_reInteger ->
        Tconst (Constant.create (1, tr_arith_bigconstant a, Bigint.zero))
    | c, [op;a;b] when c = Lazy.force coq_reBinary ->
        Tbinop (tr_binop op, tr_term uv uf a, tr_term uv uf b)
    | c, [op;a] when c = Lazy.force coq_reUnary ->
        Tunop (tr_unop op, tr_term uv uf a)
    | c, [a;b] when c = Lazy.force coq_reApply ->
        let n = tr_positive a - 1 in
        if (n < Array.length uf) then Tround (uf.(n), tr_term uv uf b)
        else raise NotGappa
    | _ ->
        raise NotGappa

let tr_const c =
  match tr_term [||] [||] c with
    | Tconst v -> v
    | _ -> raise NotGappa

let tr_pred uv uf c =
  match decompose_app c with
    | c, [l;e;u] when c = Lazy.force coq_raBound ->
        begin match decompose_app l, decompose_app u with
          | (_, [_;l]), (_, [_;u]) ->
              Pin (tr_term uv uf e, tr_const l, tr_const u)
          | _ -> raise NotGappa
        end
    | c, [er;ex;l;u] when c = Lazy.force coq_raRel ->
        Prel (tr_term uv uf er, tr_term uv uf ex, tr_const l, tr_const u)
    | c, [] when c = Lazy.force coq_raFalse ->
        let cr i = Constant.create (1, i, Bigint.zero) in
        let c0 = cr Bigint.zero in
        Pin (Tconst (cr Bigint.one), c0, c0)
    | _ ->
        raise NotGappa

let rec tr_hyps uv uf c =
  match decompose_app c with
    | _, [_;h;t] -> tr_pred uv uf h :: tr_hyps uv uf t
    | _, [_] -> []
    | _ -> raise NotGappa

let tr_var c = match kind_of_term c with
  | Var x -> string_of_id x
  | _ -> raise NotGappa

let rec tr_vars c =
  match decompose_app c with
    | _, [_;h;t] -> tr_var h :: tr_vars t
    | _, [_] -> []
    | _ -> raise NotGappa

let tr_fun c = match decompose_app c with
  | c, [rdx;fmt;mode] when c = Lazy.force coq_round ->
      let mode = match decompose_app mode with
        | c, [] when c = Lazy.force coq_rndDN -> "dn"
        | c, [] when c = Lazy.force coq_rndNE -> "ne"
        | c, [] when c = Lazy.force coq_rndUP -> "up"
        | c, [] when c = Lazy.force coq_rndZR -> "zr"
        | _ -> raise NotGappa in
      begin match decompose_app fmt with
        | c, [e;p] when c = Lazy.force coq_FLT_exp ->
            let e = tr_arith_constant e in
            let p = tr_arith_constant p in
            sprintf "float<%d,%d,%s>" p e mode
        | c, [e] when c = Lazy.force coq_FIX_exp ->
            let e = tr_arith_constant e in
            sprintf "fixed<%d,%s>" e mode
        | _ -> raise NotGappa
      end
  | _ ->
      raise NotGappa

let rec tr_funs c =
  match decompose_app c with
    | _, [_;h;t] -> tr_fun h :: tr_funs t
    | _, [_] -> []
    | _ -> raise NotGappa

let tr_goal c =
  match decompose_app c with
    | c, [uv;uf;e] when c = Lazy.force coq_convert_goal ->
        let uv = Array.of_list (tr_vars uv) in
        let uf = Array.of_list (tr_funs uf) in
        begin match decompose_app e with
          | _, [_;_;h;g] -> (tr_hyps uv uf h, tr_pred uv uf g)
          | _ -> raise NotGappa
        end
    | _ -> raise NotGappa

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
      | _ -> map_constr replace c
    in
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

let build_proof_term c nb_hyp contra =
  let bl, _ = decompose_lam c in
  let pf = List.fold_right (fun (x,t) pf -> mkApp (pf, [| var_name x |])) bl c in
  let rec aux n pf =
    if n > 0 then aux (n - 1) (mkApp (pf, [| mk_new_meta () |])) else pf
    in
  let pf = aux nb_hyp pf in
  if contra then mkApp (pf, [| Lazy.force coq_False |])
  else pf

let gappa_internal gl =
  try
    let (h, g) = tr_goal (pf_concl gl) in
    let ((emap, pf), (nb_hyp, contra)) = call_gappa (constr_of_stream gl) h g in
    let pf = evars_to_vmcast (project gl) (emap, pf) in
    let pf = build_proof_term pf nb_hyp contra in
    Tacticals.tclTHEN
      (if contra then
         Tactics.apply (Lazy.force coq_contradict_goal)
       else
         Tacticals.tclIDTAC)
      (Tacticals.tclTHEN
        (Tacticals.tclMAP (fun _ -> Tactics.introf) h)
        (Tacticals.tclTHEN (Tacmach.refine_no_check pf) Tactics.assumption)) gl
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

let gappa_quote gl =
  try
    let l = qt_hyps (pf_hyps_types gl) in
    let _R = Lazy.force coq_R in
    let _RAtom = Lazy.force coq_RAtom in
    let g = mkLApp coq_pair
      [|mkLApp coq_list [|_RAtom|]; _RAtom;
        List.fold_left (fun acc (_, h) -> mkLApp coq_cons [|_RAtom; h; acc|])
          (mkLApp coq_nil [|_RAtom|]) l;
        qt_pred (pf_concl gl)|] in
    let uv = List.fold_left (fun acc t -> mkLApp coq_cons [|_R; t; acc|])
          (mkLApp coq_nil [|_R|]) !var_list in
    let uf = List.fold_left (fun acc t -> mkLApp coq_cons [|mkArrow _R _R; t; acc|])
          (mkLApp coq_nil [|mkArrow _R _R|]) !fun_list in
    let e = mkLApp coq_convert_goal [|uv; uf; g|] in
    (*Pp.msgerrnl (Printer.pr_constr e);*)
    Hashtbl.clear var_table;
    Hashtbl.clear fun_table;
    var_list := [];
    fun_list := [];
    Tacticals.tclTHEN
      (Tacticals.tclTHEN
        (Tactics.generalize (List.map (fun (n, _) -> mkVar n) (List.rev l)))
        (Tactics.keep []))
      (Tacmach.convert_concl_no_check e DEFAULTcast) gl
  with
    | NotGappa -> error "something wrong happened"

let _ =
  Tacinterp.overwriting_add_tactic "Gappa" (fun _ -> gappa);
  Tacinterp.overwriting_add_tactic "Gappa_internal" (fun _ -> gappa_internal);
  Tacinterp.overwriting_add_tactic "Gappa_quote" (fun _ -> gappa_quote);
  Egrammar.extend_tactic_grammar "Gappa" [[Egrammar.TacTerm "gappa"]];
  Egrammar.extend_tactic_grammar "Gappa_internal" [[Egrammar.TacTerm "gappa_internal"]];
  Egrammar.extend_tactic_grammar "Gappa_quote" [[Egrammar.TacTerm "gappa_quote"]]

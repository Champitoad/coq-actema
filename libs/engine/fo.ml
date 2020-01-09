(* -------------------------------------------------------------------- *)
open Utils
open Location
open Syntax

(* -------------------------------------------------------------------- *)
type name  = string
type vname = name * int

(* -------------------------------------------------------------------- *)
type typ =
  | TVar  of vname
  | TUnit
  | TProd of typ * typ
  | TOr   of typ * typ
  | TRec  of name * typ

type expr  =
  | EVar of vname
  | EFun of name * expr list

type form =
  | FTrue
  | FFalse
  | FPred of name * expr list
  | FConn of logcon * form list
  | FBind of bkind * name * typ * form

and logcon = [ `And | `Or | `Imp | `Equiv | `Not ]
and bkind  = [ `Forall | `Exist ]

type tysig = typ list

(* -------------------------------------------------------------------- *)
type env = {
  env_prp : (name, tysig) Map.t;
}

(* -------------------------------------------------------------------- *)
module Env : sig
  val empty    : env
  val of_pvars : (name, tysig) Map.t -> env
end = struct
  let empty : env = { env_prp = Map.empty; }

  let of_pvars (pvars : (name, tysig) Map.t) : env =
    { env_prp = pvars; }
end

(* -------------------------------------------------------------------- *)
exception DuplicatedEntry of [`Prp] * name

(* -------------------------------------------------------------------- *)
module Prps : sig
  val push   : env -> name * tysig -> env
  val exists : env -> name -> bool
  val all    : env -> (name, tysig) Map.t
end = struct
  let push (env : env) ((name, sg) : name * tysig) =
    if Map.mem name env.env_prp then
      raise (DuplicatedEntry (`Prp, name));
    { env_prp = Map.add name sg env.env_prp }

  let exists (env : env) (name : name) =
    Map.mem name env.env_prp

  let all (env : env) =
    env.env_prp
end

(* -------------------------------------------------------------------- *)
exception RecheckFailure
exception TypingError

(* -------------------------------------------------------------------- *)
module VName : sig
  type bds

  val equal : bds -> vname -> vname -> bool

  module Map : sig
    val empty : bds
    val push  : bds -> name -> name -> bds
  end
end = struct
  type bds = unit

  let equal =
    assert false

  module Map = struct
    let empty =
      assert false

    let push =
      assert false
  end
end

(* -------------------------------------------------------------------- *)
module Form : sig
  val f_and   : form -> form -> form
  val f_or    : form -> form -> form
  val f_imp   : form -> form -> form
  val f_equiv : form -> form -> form
  val f_not   : form -> form

  val parity   : logcon -> int
  val check    : env -> pform -> form
  val recheck  : env -> form -> unit
  val mathml   : ?tag:string -> form -> Tyxml.Xml.elt
  val tostring : form -> string
  val tohtml   : ?id:string option -> form -> Tyxml.Xml.elt

  val t_equal : ?bds:VName.bds -> typ  -> typ  -> bool
  val e_equal : ?bds:VName.bds -> expr -> expr -> bool
  val f_equal : ?bds:VName.bds -> form -> form -> bool
end = struct
  let f_and   = fun f1 f2 -> FConn (`And  , [f1; f2])
  let f_or    = fun f1 f2 -> FConn (`Or   , [f1; f2])
  let f_imp   = fun f1 f2 -> FConn (`Imp  , [f1; f2])
  let f_equiv = fun f1 f2 -> FConn (`Equiv, [f1; f2])
  let f_not   = fun f     -> FConn (`Not  , [f])

  let t_equal =
    (* FIXME: use generated walkers *)
    let rec aux bds ty1 ty2 =
      match ty1, ty2 with
      | TVar a1, TVar a2 ->
          VName.equal bds a1 a2

      | TUnit, TUnit ->
          true
        
      | TProd (tya1, tyb1), TProd (tya2, tyb2)
      | TOr   (tya1, tyb1), TOr   (tya2, tyb2) ->
             aux bds tya1 tya2
          && aux bds tyb1 tyb2

      | TRec (a1, ty1), TRec (a2, ty2) ->
          aux (VName.Map.push bds a1 a2) ty1 ty2

      | _, _ ->
          false

    in fun ?(bds = VName.Map.empty) ty1 ty2 -> aux bds ty1 ty2

  let e_equal =
    let rec aux bds e1 e2 =
      match e1, e2 with
      | EVar x1, EVar x2 ->
          VName.equal bds x1 x2

      | EFun (f1, es1), EFun (f2, es2) 
            when List.length es1 = List.length es2
        ->
          (f1 = f2) && List.for_all2 (aux bds) es1 es2

      | _, _ ->
          false

    in fun ?(bds = VName.Map.empty) e1 e2 -> aux bds e1 e2

  let f_equal =
    let rec aux bds f1 f2 =
      match f1, f2 with
      | FTrue , FTrue
      | FFalse, FFalse -> true

      | FPred (p1, es1), FPred (p2, es2)
          when List.length es1 = List.length es2
        -> (p1 = p2) && List.for_all2 (e_equal ~bds) es1 es2

      | FConn (c1, fs1), FConn (c2, fs2)
          when List.length fs1 = List.length fs2
        -> (c1 = c2) && List.for_all2 (aux bds) fs1 fs2

      | FBind (b1, x1, ty1, f1), FBind (b2, x2, ty2, f2) ->
            (b1 = b2)
         && t_equal ty1 ty2
         && aux (VName.Map.push bds x1 x2) f1 f2

      | _, _ ->
          false

    in fun ?(bds = VName.Map.empty) f1 f2 -> aux bds f1 f2

  let parity (lg : logcon) =
    match lg with
    | `And -> 2 | `Or -> 2 | `Imp -> 2 | `Equiv -> 2 | `Not -> 1

  let rec recheck (env : env) (form : form) : unit =
    match form with
    | FTrue | FFalse -> ()

    | FPred (name, []) ->
        if not (Prps.exists env name) then
          raise RecheckFailure

    | FConn (lg, forms) ->
        List.iter (recheck env) forms;
        if List.length forms <> parity lg then
          raise RecheckFailure

    | _ ->
        raise RecheckFailure    (* FIXME *)

  let rec check (env : env) (form : pform) =
    let pred name fs = FConn (name, List.map (check env) fs) in

    match unloc form with
    | PFCst true  -> FTrue
    | PFCst false -> FFalse

    | PFAnd   (f1, f2) -> pred `And   [f1; f2]
    | PFOr    (f1, f2) -> pred `Or    [f1; f2]
    | PFImp   (f1, f2) -> pred `Imp   [f1; f2]
    | PFEquiv (f1, f2) -> pred `Equiv [f1; f2]
    | PFNot   f1       -> pred `Not   [f1]

    | PFVar name ->
        if not (Prps.exists env (unloc name)) then
          raise TypingError;
        FPred (unloc name, [])

  let rec prio_of_form = function
    | FTrue         -> max_int
    | FFalse        -> max_int
    | FPred  _      -> max_int
    | FConn (op, _) -> prio_of_op op
    | _             -> assert false (* FIXME *)

  and prio_of_op = function
    | `Not   -> prio_Not
    | `And   -> prio_And
    | `Or    -> prio_Or
    | `Imp   -> prio_Imp
    | `Equiv -> prio_Equiv

  and prio_Not   = 5
  and prio_And   = 4
  and prio_Or    = 3
  and prio_Imp   = 2
  and prio_Equiv = 1

  let mathml =
    let open Tyxml in

    let mi ?(sherif = false) c =
      let st = Xml.string_attrib "mathvariant" "sans-serif" in
      let a  = if sherif then [st] else [] in
      Xml.node ~a "mi" [c] in

    let pr doit c =
      let sc   = Xml.string_attrib "stretchy" "false" in
      let mo c = Xml.node ~a:[sc] "mo" [Xml.pcdata c] in
      if doit then [mo "("] @ c @ [mo ")"] else c in

    let spaced c =
      let a = Xml.string_attrib "width" "thickmathspace" in
      let x = Xml.node ~a:[a] "mspace" [] in
      [x] @ c @ [x] in

    let rec for_form (form : form) =
      match form with
      | FTrue ->
          [mi (Xml.entity "#x22A4")]

      | FFalse ->
          [mi (Xml.entity "#x22A5")]

      | FConn (lg, fs) -> begin
          let fs = List.map (fun x -> (prio_of_form x, for_form x)) fs in

          match lg, fs with
          | `And, [(p1, f1); (p2, f2)] ->
                (pr (p1 < prio_And) f1)
              @ [mi (Xml.entity "#x2227")]
              @ (pr (p2 <= prio_And) f2)
          | `Or , [(p1, f1); (p2, f2)] ->
                (pr (p1 < prio_Or) f1)
              @ [mi (Xml.entity "#x2228")]
              @ (pr (p2 <= prio_Or) f2)
          | `Imp, [(p1, f1); (p2, f2)] ->
                (pr (p1 <= prio_Imp) f1)
              @ (spaced [mi (Xml.entity "#x27F9")])
              @ (pr (p2 < prio_Imp) f2)
          | `Equiv, [(p1, f1); (p2, f2)] ->
                (pr (p1 <= prio_Equiv) f1)
              @ (spaced [mi (Xml.entity "#x27FA")])
              @ (pr (p2 <= prio_Equiv) f2)
          | `Not, [(p, f)] ->
              [mi (Xml.entity "#x00AC")] @ (pr (p < prio_Not) f)
          | (`And | `Or | `Imp | `Not | `Equiv), _ ->
              assert false
        end

      | FPred (name, []) ->
          [mi ~sherif:true (Xml.pcdata name)]

      | _ ->
          assert false          (* FIXME *)

    in fun ?(tag : string option) (form : form) ->
       let xmlns   = "http://www.w3.org/1998/Math/MathML" in
       let xmlns   = Xml.string_attrib "xmlns" xmlns in
       let display = Xml.string_attrib "display" "block" in
       let tag     =
         match tag with
         | None     -> []
         | Some tag -> [Xml.string_attrib "style" tag]
       in
       let output  = Xml.node "mstyle" (for_form form) in
       let output  = Xml.node ~a:([xmlns; display] @ tag) "math" [output] in

       output

  let tostring =
    let pr doit c =
      if doit then Format.sprintf "(%s)" c else c in

    let spaced ?(left = true) ?(right = true) c =
      Format.sprintf "%s%s%s"
        (if left then " " else "") c (if right then " " else "") in

    let rec for_form (form : form) =
      match form with
      | FTrue ->
          UTF8.of_char (UChar.chr 0x22A4)

      | FFalse ->
          UTF8.of_char (UChar.chr 0x22A5)

      | FConn (lg, fs) -> begin
          let fs = List.map (fun x -> (prio_of_form x, for_form x)) fs in

          match lg, fs with
          | `And, [(p1, f1); (p2, f2)] ->
                (pr (p1 < prio_And) f1)
              ^ (spaced (UTF8.of_char (UChar.chr 0x2227)))
              ^ (pr (p2 <= prio_And) f2)
          | `Or , [(p1, f1); (p2, f2)] ->
                (pr (p1 < prio_Or) f1)
              ^ (spaced (UTF8.of_char (UChar.chr 0x2228)))
              ^ (pr (p2 <= prio_Or) f2)
          | `Imp, [(p1, f1); (p2, f2)] ->
                (pr (p1 <= prio_Imp) f1)
              ^ (spaced (UTF8.of_char (UChar.chr 0x27F9)))
              ^ (pr (p2 < prio_Imp) f2)
          | `Equiv, [(p1, f1); (p2, f2)] ->
                (pr (p1 <= prio_Equiv) f1)
              ^ (spaced (UTF8.of_char (UChar.chr 0x27FA)))
              ^ (pr (p2 <= prio_Equiv) f2)
          | `Not, [(p, f)] ->
                (spaced ~left:false (UTF8.of_char (UChar.chr 0x00AC)))
              ^ (pr (p < prio_Not) f)
          | (`And | `Or | `Imp | `Not | `Equiv), _ ->
              assert false
        end

      | FPred (name, []) ->
          UTF8.of_latin1 name

      | _ ->
          assert false          (* FIXME *)

    in fun (form : form) -> for_form form

  let tohtml ?(id : string option option) =
    let open Tyxml in

    let pr doit c =
      if doit then [Xml.pcdata "("] @ c @ [Xml.pcdata ")"] else c in

    let spaced ?(left = true) ?(right = true) c =
      let c = if left  then [Xml.pcdata " "] @ c else c in
      let c = if right then c @ [Xml.pcdata " "] else c in
      c in

    let rec for_form (p : int list) (form : form) =
      let data =
        match form with
        | FTrue ->
            [Xml.entity "#x22A4"]
  
        | FFalse ->
            [Xml.entity "#x22A5"]
  
        | FConn (lg, fs) -> begin
            let fs =
              List.mapi
                (fun i x -> (prio_of_form x, for_form (i :: p) x))
                fs in
  
          match lg, fs with
          | `And, [(p1, f1); (p2, f2)] ->
                (pr (p1 < prio_And) f1)
              @ (spaced [Xml.entity "#x2227"])
              @ (pr (p2 <= prio_And) f2)
          | `Or , [(p1, f1); (p2, f2)] ->
                (pr (p1 < prio_Or) f1)
              @ (spaced [Xml.entity "#x2228"])
              @ (pr (p2 <= prio_Or) f2)
          | `Imp, [(p1, f1); (p2, f2)] ->
                (pr (p1 <= prio_Imp) f1)
              @ (spaced [Xml.entity "#x27F9"])
              @ (pr (p2 < prio_Imp) f2)
          | `Equiv, [(p1, f1); (p2, f2)] ->
                (pr (p1 <= prio_Equiv) f1)
              @ (spaced [Xml.entity "#x27FA"])
              @ (pr (p2 <= prio_Equiv) f2)
          | `Not, [(p, f)] ->
                (spaced ~left:false [Xml.entity "#x00AC"])
              @ (pr (p < prio_Not) f)
          | (`And | `Or | `Imp | `Not | `Equiv), _ ->
              assert false
        end

        | FPred (name, []) ->
            [Xml.pcdata (UTF8.of_latin1 name)]

        | _ ->
            assert false        (* FIXME *)

      in

      let thisid =
        id |> Option.map (fun prefix ->
          let p = String.concat "/" (List.rev_map string_of_int p) in
          Option.fold
            (fun p prefix -> Format.sprintf "%s:%s" prefix p)
            p prefix) in
      let thisid = thisid |> Option.map (fun x -> Xml.string_attrib "id" x) in

      [Xml.node ~a:(List.of_option thisid) "span" data] in

    fun (form : form) ->
      Xml.node "span" (for_form [] form)

end

(* -------------------------------------------------------------------- *)
module Goal : sig
  val check : pgoal -> env * form
end = struct
  let check ((ps, f) : pgoal) =
    let env =
      let pvars = List.map (fun x -> (unloc x, [])) ps in
      Env.of_pvars (Map.of_enum (List.enum pvars)) in
    (env, Form.check env f)
end

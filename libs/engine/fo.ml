(* -------------------------------------------------------------------- *)
open Utils
open Location
open Syntax

(* -------------------------------------------------------------------- *)
type name = string

type env = {
  env_prp : name Set.t;
}

(* -------------------------------------------------------------------- *)
module Env : sig
  val empty    : env
  val of_pvars : name Set.t -> env
end = struct
  let empty : env = { env_prp = Set.empty; }

  let of_pvars (pvars : name Set.t) : env =
    { env_prp = pvars; }
end

(* -------------------------------------------------------------------- *)
exception DuplicatedEntry of [`Prp] * name

(* -------------------------------------------------------------------- *)
module Prps : sig
  val push   : env -> name -> env
  val exists : env -> name -> bool
  val all    : env -> name Set.t
end = struct
  let push (env : env) (name : name) =
    if Set.mem name env.env_prp then
      raise (DuplicatedEntry (`Prp, name));
    { env_prp = Set.add name env.env_prp }

  let exists (env : env) (name : name) =
    Set.mem name env.env_prp

  let all (env : env) =
    env.env_prp
end

(* -------------------------------------------------------------------- *)
type form =
  | FTrue
  | FFalse
  | FVar  of name
  | FConn of logcon * form list

and logcon  = [ `And | `Or | `Imp | `Equiv | `Not ]

(* -------------------------------------------------------------------- *)
exception RecheckFailure
exception TypingError

(* -------------------------------------------------------------------- *)
module Form : sig
  val f_false : form
  val f_true  : form
  val f_and   : form -> form -> form
  val f_or    : form -> form -> form
  val f_imp   : form -> form -> form
  val f_equiv : form -> form -> form
  val f_not   : form -> form

  val f_ands : form list -> form
  val f_ors  : form list -> form
  val f_imps : form list -> form -> form

  val parity   : logcon -> int
  val check    : env -> pform -> form
  val recheck  : env -> form -> unit
  val mathml   : ?tag:string -> form -> Tyxml.Xml.elt
  val tostring : form -> string
  val tohtml   : ?id:string option -> form -> Tyxml.Xml.elt

  val equal : form -> form -> bool

  val flatten_disjunctions : form -> form list
  val flatten_conjunctions : form -> form list
end = struct
  let f_and   = fun f1 f2 -> FConn (`And  , [f1; f2])
  let f_or    = fun f1 f2 -> FConn (`Or   , [f1; f2])
  let f_imp   = fun f1 f2 -> FConn (`Imp  , [f1; f2])
  let f_equiv = fun f1 f2 -> FConn (`Equiv, [f1; f2])
  let f_not   = fun f     -> FConn (`Not  , [f])

  let equal = ((=) : form -> form -> bool)

  let f_false : form = FFalse
  let f_true  : form = FTrue

  let f_ands (fs : form list) : form =
    match fs with
    | []      -> f_true
    | [f]     -> f
    | f :: fs -> List.fold_left f_and f fs

  let f_ors (fs : form list) : form =
    match fs with
    | []      -> f_false
    | [f]     -> f
    | f :: fs -> List.fold_left f_or f fs

  let f_imps (fs : form list) (f : form) =
    List.fold_right f_imp fs f

  let flatten_disjunctions =
    let rec doit acc f =
      match f with
      | FConn (`Or, [f1; f2]) -> doit (f2 :: acc) f1
      | _ -> f :: acc
    in fun f -> doit [] f

  let flatten_conjunctions =
    let rec doit acc f =
      match f with
      | FConn (`And, [f1; f2]) -> doit (f2 :: acc) f1
      | _ -> f :: acc
    in fun f -> doit [] f

  let parity (lg : logcon) =
    match lg with
    | `And -> 2 | `Or -> 2 | `Imp -> 2 | `Equiv -> 2 | `Not -> 1

  let rec recheck (env : env) (form : form) : unit =
    match form with
    | FTrue | FFalse -> ()

    | FVar name ->
        if not (Prps.exists env name) then
          raise RecheckFailure

    | FConn (lg, forms) ->
        List.iter (recheck env) forms;
        if List.length forms <> parity lg then
          raise RecheckFailure

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
        FVar (unloc name)

  let rec prio_of_form = function
    | FTrue         -> max_int
    | FFalse        -> max_int
    | FVar  _       -> max_int
    | FConn (op, _) -> prio_of_op op

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

      | FVar name ->
          [mi ~sherif:true (Xml.pcdata name)]

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

      | FVar name ->
          UTF8.of_latin1 name

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

        | FVar name ->
            [Xml.pcdata (UTF8.of_latin1 name)]

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
    let env = Env.of_pvars (Set.of_list (List.map unloc ps)) in
    (env, Form.check env f)
end

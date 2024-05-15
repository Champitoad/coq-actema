open Api_new
open Lang
open QCheck2

(******************************************************************************)
(** Testing utilities. *)

(** Generate a context and a typed term in this context. *)
let term_in_context =
  let open Gen in
  let* context = TermGen.context Env.test_env in
  let* term, ty = TermGen.typed ~context Env.test_env in
  return (context, term, ty)

let print_term = Notation.term_to_string Env.test_env

let print_context ctx =
  let bindings =
    List.map (Print.pair Name.show Term.show) @@ Context.to_list ctx
  in
  "[" ^ String.concat ", " bindings ^ "]"

let print_term_in_context (ctx, term, ty) =
  (Print.triple print_context
     (Notation.term_to_string Env.test_env ~ctx)
     print_term)
    (ctx, term, ty)

(******************************************************************************)
(** Random term generation tests. *)

(** Test that the well-typed term generator indeed produces well-typed terms. *)
let test_typed_gen =
  Test.make ~name:"typed_term_gen" term_in_context
    ~print:(Print.triple print_context print_term print_term)
    begin
      fun (ctx, term, ty) -> Typing.check ~context:ctx Env.test_env term = ty
    end

(** Test weakening. *)
let test_weakening =
  Test.make ~name:"weakening"
    (Gen.pair (TermGen.context Env.test_env) (TermGen.typed Env.test_env))
    ~print:(Print.pair print_context (Print.pair print_term print_term))
    begin
      fun (ctx, (term, ty)) ->
        Typing.check Env.test_env term = ty
        && Typing.check ~context:ctx Env.test_env term = ty
    end

(** Test the substitution lemma. *)
let test_substitution =
  Test.make ~name:"substitution-lemma" term_in_context
    ~print:print_term_in_context ~count:10000
    begin
      fun (ctx, term, ty) ->
        QCheck2.assume (Context.size ctx > 0);
        let _, v_ty = Option.get @@ Context.get 0 ctx in
        let ctx = Option.get @@ Context.pop ctx in
        let term', _ =
          Gen.generate1 (TermGen.typed ~context:ctx ~ty:v_ty Env.test_env)
        in
        Typing.check ~context:ctx Env.test_env (TermUtils.subst 0 term' term)
        = ty
    end

(******************************************************************************)
(** Notation tests. *)

(** Split a string based on whitespace (and remove the whitespace). *)
let words (str : string) : string list =
  let curr_str curr = String.of_seq @@ List.to_seq @@ List.rev curr in
  let rec loop (chars : char list) (curr : char list) (acc : string list) =
    match chars with
    | [] -> if curr <> [] then List.rev (curr_str curr :: acc) else List.rev acc
    (* Reset [curr]. *)
    | c :: chars when c = ' ' || c = '\n' || c = '\t' ->
        if curr <> []
        then loop chars [] (curr_str curr :: acc)
        else loop chars [] acc
    (* Extend [curr]. *)
    | c :: chars -> loop chars (c :: curr) acc
  in
  loop (List.of_seq @@ String.to_seq str) [] []

(** Printing a term to a string should not depend on the string width,
    except for whitespace. *)
let test_pp_term_string =
  Test.make ~name:"pp_term_string"
    (Gen.triple
       (TermGen.simple ~closed:true Env.test_env)
       Gen.small_nat Gen.small_nat)
    ~print:(Print.triple Term.show Print.int Print.int)
    begin
      fun (t, w1, w2) ->
        let str1 = Notation.term_to_string ~width:w1 Env.test_env t in
        let str2 = Notation.term_to_string ~width:w2 Env.test_env t in
        words str1 = words str2
    end

(****************************************************************************)
(** Run the tests. *)

let () =
  Alcotest.run "Actema Lang Tests"
    [ ( "generator-tests"
      , List.map QCheck_alcotest.to_alcotest [ test_typed_gen ] )
    ; ( "typing-tests"
      , List.map QCheck_alcotest.to_alcotest
          [ test_weakening; test_substitution ] )
    ; ( "notation-tests"
      , List.map QCheck_alcotest.to_alcotest [ test_pp_term_string ] )
    ]

open Api_new
open Lang
open QCheck2

(******************************************************************************)
(** Random term generation tests. *)

(** Test that the well-typed term generator indeed produces only well-typed terms. *)
let test_typed_gen =
  Test.make ~name:"typed_term_gen"
    (TermGen.typed ~closed:true Env.test_env Term.mkProp)
    ~print:Term.show
    begin
      fun t -> Typing.check Env.test_env t = Term.mkProp
    end

(** Test weakening. *)
(*let test_weakening =
  Test.make ~name:"weakening" (Gen.pair (TermGen.typed test_env Term.mkProp) )
    ~print:Term.show
    begin fun t ->
    end*)

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
       (TermGen.simple ~closed:false Env.test_env)
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
    ; ( "notation-tests"
      , List.map QCheck_alcotest.to_alcotest [ test_pp_term_string ] )
    ]

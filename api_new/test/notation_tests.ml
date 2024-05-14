open Api_new
open Lang
open QCheck2

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
    (Gen.triple TermGen.simple Gen.small_nat Gen.small_nat)
    ~print:(Print.triple Term.show Print.int Print.int)
    begin
      fun (t, w1, w2) ->
        let str1 = Notation.term_to_string ~width:w1 Env.empty t in
        let str2 = Notation.term_to_string ~width:w2 Env.empty t in
        words str1 = words str2
    end

(****************************************************************************)
(** Run the tests. *)

let () =
  let tests = List.map QCheck_alcotest.to_alcotest [ test_pp_term_string ] in
  Alcotest.run "Notation Tests" [ ("pp-string", tests) ]

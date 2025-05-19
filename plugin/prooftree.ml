open Utils.Pervasive
open Api
    
(* the type for prooftrees *)
(* 'a for actions, 'g for goals *)
type tree =
    Tree of Logic.goal * goal_state ref
and (* and list of mutable subgoals *)
    goal_state =
  | Open
  | Node of Logic.action * (tree list);;

(* the goals list points to the leafs in the tree *)
type proofTree =
  {tree : tree;
   mutable goals : (Logic.goal * goal_state ref) list;
   mutable history :  (goal_state ref * ((Logic.goal * (goal_state ref) ) list)) list };;


let newtree c =
  let r : goal_state ref = ref Open in
  (Tree (c, r), r);;

let newProofTree c =
  let t,r = newtree c in
  {tree = t; goals = [c,r]; history = [] };;

let get_subgoal t n =
  match (List.nth t.goals n) with
    (g,_) -> g;;

let term_to_subgoal =
  List.map (fun p -> Tree (p, ref Open));; 

let update_goal_t s a l =
  match !s with
  | Node _ -> failwith "update"
  | Open ->
      s := Node (a, l);;

let split l n =
  let rec aux n acc = function
    | [] -> failwith "split"
    | a::l ->
      if n = 0
      then (List.rev acc, l,a)
      else aux (n-1) (a::acc) l
  in aux n [] l;;

let rec get_subgoals = function
  | Tree (p, r) ->
    match !r with
    | Open -> [p,r]
    | Node (_,l) -> get_subgoals_aux l
and get_subgoals_aux = function
  | [] -> []
  | t::l -> (get_subgoals t)@(get_subgoals_aux l)

let perform n a l t = 
  let l = term_to_subgoal l in
  let (l1, l2, (g,r)) = split t.goals n in
  update_goal_t r a l;
  t.history <- (r, t.goals)::t.history;
  t.goals <- get_subgoals t.tree

let undo_t t =
  match t.history with
  | [] -> failwith "undo"
  | (r, _)::l ->
    r := Open;
    t.goals <- get_subgoals t.tree;
    t.history <- l;;
 

let rec size (Tree (_, r)) =
   match !r with
  | Open -> 0
  | Node (a,l) ->
    1 + (List.fold_left (fun n a -> n + (size a)) 0 l);;


let  action_to_string = Logic.show_action
let  term_to_string t = Lang.Term.show t

(*
type pregoal =
  { g_env : Env.t; g_vars : Vars.t; g_hyps : Hyps.t; g_concl : Term.t }
*)


let  pregoal_to_string (g : Logic.pregoal) = Lang.Term.show g.g_concl
let  goal_to_string (g : Logic.goal) = Lang.Term.show g.g_pregoal.g_concl

(* Human-readable descriptions of actions *)
let string_of_action = function
  | Logic.AId -> "That did nothing XD."
  | Logic.ADuplicate name -> "Duplicate hypothesis " ^ (Name.show name)
  | Logic.AClear name -> "Clear hypothesis " ^ (Name.show name)
  | Logic.AExact name -> "The solution is trivial with " ^ (Name.show name)
  | Logic.AIntro n -> "Let us introduce " ^ string_of_int n ^ " variables/hypotheses."
  | Logic.AElim (name, n) -> "Break down " ^ (Name.show name) ^ " by elimination."
  | Logic.ASimpl path -> "Simplifying at " ^ (Logic.Path.to_string path)
  | Logic.ACase term -> "We look into the different cases for " ^ (Lang.Term.show term) ^ "."
  | Logic.ACaseIntro n -> "Introduce case " ^ (string_of_int n)
  | Logic.AInd term -> "Apply induction on " ^ (Lang.Term.show term)
  | Logic.AIndIntro n -> "Introduce induction case " ^ (string_of_int n)
  | Logic.AGeneralize name -> "We generalize " ^ (Name.show name)
  | Logic.ALemmaAdd name -> "Introduce lemma " ^ (Name.show name)
  | Logic.ADnD (path1, path2, _, kind) ->
      let kind_str = match kind with
        | Logic.Subform -> "combining"
        | Logic.RewriteL -> "rewriting left-to-right with"
        | Logic.RewriteR -> "rewriting right-to-left with"
      in
      "By " ^ kind_str ^ " " ^ (Logic.Path.to_string path1) ^ 
      " and " ^ (Logic.Path.to_string path2)
  | Logic.AInstantiate (term, paths) ->
      "Instantiate " ^ (Lang.Term.show term) ^ " with " ^
      (String.concat ", " (List.map Logic.Path.to_string paths))

(* Text tree representation for displaying proof trees *)
type text_tree =
  | Text of string * string * text_tree list
  | Empty

(* Convert the prooftree to a displayable text tree *)
let rec tree_to_text_tree (Tree (goal, state_ref)) =
  let goal_str = goal_to_string goal in
  match !state_ref with
  | Open -> Text (goal_str, "Goal is still open", [])
  | Node (action, subtrees) ->
      let action_str = string_of_action action in
      let child_trees = List.map tree_to_text_tree subtrees in
      Text (goal_str, action_str, child_trees)

(* Convert entire proof tree to text tree *)
let prooftree_to_text_tree pt =
  tree_to_text_tree pt.tree

(* Print a text tree with indentation *)
let rec print_text_tree ?(indent=0) t =
  match t with
  | Empty -> ()
  | Text (goal, action, children) ->
      print_endline (String.make indent ' ' ^ "Goal: " ^ goal);
      print_endline (String.make (indent+2) ' ' ^ "Action: " ^ action);
      List.iter (print_text_tree ~indent:(indent+4)) children

(* Concatenate text tree into a single string *)
let rec concat_text_tree t =
  match t with
  | Empty -> ""
  | Text (goal, action, children) ->
      "Goal: " ^ goal ^ "\nAction: " ^ action ^ 
      (if children = [] 
       then "\nThis branch is DONE!\n" 
       else "\n" ^ String.concat "\n" (List.map concat_text_tree children))

(* Adapter to convert between old and new tree formats for backward compatibility *)
let change_trees (tree : tree) =
  tree_to_text_tree tree

(* Get a summary of the proof tree *)
let summarize_prooftree pt =
  let total_nodes = size pt.tree in
  let open_goals = List.length pt.goals in
  let history_steps = List.length pt.history in
  Printf.sprintf "Proof tree with %d total steps, %d open goals, and %d steps in history"
    total_nodes open_goals history_steps

(* Convert text_tree to string with proper indentation *)
let string_of_text_tree tt =
  let buf = Buffer.create 256 in
  let rec aux ?(indent=0) t =
    match t with
    | Empty -> ()
    | Text (goal, action, children) ->
        Buffer.add_string buf (String.make indent ' ' ^ "Goal: " ^ goal ^ "\n");
        Buffer.add_string buf (String.make (indent+2) ' ' ^ "Action: " ^ action ^ "\n");
        List.iter (aux ~indent:(indent+4)) children
  in
  aux tt;
  Buffer.contents buf

(* Get proof summary as a string instead of printing it *)
let get_proof_summary pt =
  let tt = prooftree_to_text_tree pt in
  let summary = 
    "Proof Tree Summary:\n" ^
    (summarize_prooftree pt) ^ "\n\n" ^
    "Detailed Proof Structure:\n" ^
    (string_of_text_tree tt) ^ "\n\n" ^
    "Textual Explanation:\n" ^
    (concat_text_tree tt)
  in
  summary

(* Function that prints the proof summary using Log *)
(* let print_proof_summary pt =
  Log.printf "%s" (get_proof_summary pt) 

(* Example: Create and print a simple proof tree using the socrates example *)
let create_sample_socrates () =
  match Logic.parse_goal "forall x, Human x -> Mortal x" with
  | None -> print_endline "Failed to parse sample goal"
  | Some goal ->
      let pt = newProofTree goal in
      (* We would add actual proof steps here *)
      print_proof_summary pt

(* For backward compatibility with existing code *)
let () =
  (* Create a simple example tree and print it *)
  match Logic.parse_goal "forall x, x = x" with
  | None -> print_endline "Failed to parse example goal"
  | Some goal ->
      let pt = newProofTree goal in
      let tt = change_trees pt.tree in
      print_text_tree tt;
      let all_text = concat_text_tree tt in
      print_endline all_text

  *)

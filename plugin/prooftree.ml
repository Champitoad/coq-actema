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
  match (List.nth t.goals (n-1)) with
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

let rec remove k l =
  if k = 0 then l
  else match l with
    | _::l -> remove (k-1) l
    | _ -> failwith "remove"

let rec keep_aux k l =
  if k = 0 then []
  else match l with
    | x::l -> x::(keep_aux (k-1) l)
    | _ -> failwith "keep"

let keep i j l =
  keep_aux j (remove i l)

let perform n a nl t = 
  let nl = term_to_subgoal nl in
  let ol = get_subgoals t.tree in
  let (_,r) = List.nth ol n in
  let nn = List.length nl in
  let on = List.length ol in
  if nn  < on -1
  then failwith "number goals"
   else
    let ngl = keep n (nn - on + 1) nl in
    update_goal_t r a ngl;
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

let rec outline = function
  | Open -> "XX"
  | Node (a, l) ->
    let sl = List.map (fun (Tree (_,x)) -> (outline !x)^" ") l in
    let sl = List.fold_left (fun s1 s2 -> s1 ^ s2) "" sl  
    in "a(" ^ sl ^ ")"

let  action_to_string = Logic.show_action
let  term_to_string t = Notation.term_to_string t

(*
type pregoal =
  { g_env : Env.t; g_vars : Vars.t; g_hyps : Hyps.t; g_concl : Term.t }
*)

(*    Notation.term_to_string *)


let  pregoal_to_string (g : Logic.pregoal) =
         Lang.Term.show  g.g_concl

let  goal_to_string (g : Logic.goal) = pregoal_to_string g.g_pregoal

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
  | Open -> Text (goal_str, "Goal is still unfinished", [])
  | Node (action, subtrees) ->
      let action_str = string_of_action action in
      let child_trees = List.map tree_to_text_tree subtrees in
      Text (goal_str, action_str, child_trees)

(* Convert entire proof tree to text tree *)
let prooftree_to_text_tree pt =
  tree_to_text_tree pt.tree

let rec print_text_tree_aux level t =
  match t with
  | Empty -> ""
  | Text (goal, action, children) ->
      let current_line = String.make (level * 2) ' ' ^ "Action: " ^ action ^ "\n" in
      if children = [] then
        current_line ^ "No more subgoals.\n"
      else
        let children_text = String.concat "\n" 
          (List.map (fun x -> print_text_tree_aux (level + 1) x) children) in
        current_line ^ children_text

let print_text_tree t = print_text_tree_aux 0 t

let rec summarize_tree (Tree (goal, state_ref)) =
  match !state_ref with
  | Open -> ""  (* Skip open goals entirely *)
  | Node (action, children) ->
      let action_str = string_of_action action in
      let children_str = 
        String.concat "" 
          (List.filter (fun s -> s <> "") 
            (List.map (fun t -> "  " ^ summarize_tree t) children))
      in
      if children_str = "" then
        action_str ^ "\n" ^ "  Proof completed\n"
      else
        action_str ^ "\n" ^ children_str

(*unused from here downwards*)

let summarize_prooftree pt =
  let total_nodes = size pt.tree in
  let open_goals = List.length pt.goals in
  let history_steps = List.length pt.history in
  Printf.sprintf "Proof tree with %d total steps, %d open goals, and %d steps in history\n%s"
    total_nodes open_goals history_steps (summarize_tree pt.tree)

(*  Serching For an issue with the tree structure


let count_direct_children (Tree (_, state_ref)) =
  match !state_ref with
  | Open -> 0
  | Node (_, subtrees) -> List.length subtrees;;

let rec print_raw_tree_depth depth (Tree (_, state_ref)) =
  let indent = String.make (depth * 2) ' ' in
  match !state_ref with
  | Open -> 
      Printf.sprintf "%s0\n" indent
  | Node (_, subtrees) ->
      let direct_children = List.length subtrees in
      Printf.sprintf "%s%d\n%s" 
        indent 
        direct_children 
        (String.concat "" (List.map (print_raw_tree_depth (depth + 1)) subtrees));;

let print_raw_prooftree pt =
  Printf.sprintf "=== Tree Direct Children Count ===\n%s===========================\n"
    (print_raw_tree_depth 0 pt.tree);;
*)


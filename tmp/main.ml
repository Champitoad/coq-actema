open QCheck
open Api.Logic

let return = Gen.return
let ( let* ) = Gen.( >>= )

(*let choose xs =
  if Array.length xs = 0 then failwith "choose : empty list"
  else
    let idx = Random.int (Array.length xs) in
    xs.(idx)*)

let gen_tiny_list (gen : 'a Gen.t) : 'a list Gen.t =
  let* length = Gen.int_range 0 3 in
  Gen.list_repeat length gen

let gen_type : type_ Gen.t =
  let* name = Gen.string_small_of Gen.printable in
  return @@ TVar name

let gen_expr : expr Gen.t =
  let rec aux n : expr Gen.t =
    let evar : expr Gen.t =
      begin
        let* name = Gen.string_small_of Gen.printable in
        return @@ EVar name
      end
    in
    let efun : expr Gen.t =
      begin
        let* name = Gen.string_small_of Gen.printable in
        let* exprs = gen_tiny_list @@ aux (n - 1) in
        return @@ EFun (name, exprs)
      end
    in
    if n <= 0 then evar else Gen.oneof [ evar; efun ]
  in
  aux 20

let gen_form : form Gen.t =
  let rec aux n : form Gen.t =
    let ftrue : form Gen.t = return @@ FTrue in
    let ffalse : form Gen.t = return @@ FFalse in
    let fpred : form Gen.t =
      let* name = Gen.string_small_of Gen.printable in
      let* exprs = gen_tiny_list gen_expr in
      return @@ FPred (name, exprs)
    in
    let fconn : form Gen.t =
      let* logcon = Gen.oneofl [ And; Or; Imp; Equiv; Not ] in
      let* forms = gen_tiny_list @@ aux (n - 1) in
      return @@ FConn (logcon, forms)
    in
    let fbind : form Gen.t =
      let* bkind = Gen.oneofl [ Forall; Exist ] in
      let* name = Gen.string_small_of Gen.printable in
      let* ty = gen_type in
      let* form = aux (n - 1) in
      return @@ FBind (bkind, name, ty, form)
    in
    if n <= 0 then Gen.oneof [ ftrue; ffalse ] else Gen.oneof [ ftrue; ffalse; fpred; fconn; fbind ]
  in
  aux 20

let gen_lemma : lemma Gen.t =
  let* l_full = Gen.string_small_of Gen.printable in
  let* l_user = Gen.string_small_of Gen.printable in
  let* l_stmt = gen_form in
  return { l_full; l_user; l_stmt }

(** Time a function on a list of inputs. *)
let time tag f xs =
  let start = Sys.time () in
  let res = List.map f xs in
  let stop = Sys.time () in
  Format.printf "[%s] %.3fs\n" tag (stop -. start);
  res

let () =
  let lemmas = Gen.generate ~n:100000 gen_lemma in

  (* Time the Marshal bytes version. *)
  let bytes = time "encode-marshal-bytes" (fun l -> Marshal.to_bytes l []) lemmas in
  let res1 =
    time "decode-marshal-bytes" (fun (b : bytes) : lemma -> Marshal.from_bytes b 0) bytes
  in

  Format.printf "\n";

  (* Time the Marshal string version. *)
  let strings = time "encode-marshal-string" (fun l -> Marshal.to_string l []) lemmas in
  let res2 =
    time "decode-marshal-string" (fun (str : string) : lemma -> Marshal.from_string str 0) strings
  in

  Format.printf "\nEqual : %b %b\n" (lemmas = res1) (lemmas = res2)

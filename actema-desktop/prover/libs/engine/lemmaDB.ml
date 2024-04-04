open Utils

type t = 
  { db_env : Fo.env
  ; db_map : (string, Fo.form) Map.t
  }

exception LemmaNotFound of string

let env db =
  db.db_env

let get db name =
  Option.get_exn
    (Map.find_opt name db.db_map)
    (LemmaNotFound name)

let empty env =
  { db_env = env; db_map = Map.empty }
    
let add db name form =
  { db with db_map = Map.add name form db.db_map }

let all_lemmas db =
  Map.bindings db.db_map

let filter pred db = 
  { db with db_map = Map.filter pred db.db_map}

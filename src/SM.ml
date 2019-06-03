open GT       
open Language
open List
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter
     val eval : config -> prg -> config
   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let eval config prog =
  let eval' (stack, (state, is, os)) = function
    | BINOP op ->
      let y :: x :: xs = stack and f = Expr.parseOperation op
      in (f x y :: xs, (state, is, os))
    | CONST c -> (c :: stack, (state, is, os))
    | READ -> (hd is :: stack, (state, tl is, os))
    | WRITE -> (tl stack, (state, is, os @ [hd stack]))
    | LD name -> (state name :: stack, (state, is, os))
    | ST name -> (tl stack, (Expr.update name (hd stack) state, is, os))
  in fold_left eval' config prog

(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o
let rec compileExpr = function
  | Expr.Const c -> [CONST c]
  | Expr.Var name -> [LD name]
  | Expr.Binop (op, x, y) -> compileExpr x @ compileExpr y @ [BINOP op]
(* Stack machine compiler
     val compile : Language.Stmt.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile = function
  | Stmt.Read var -> [READ; ST var]
  | Stmt.Write expr -> compileExpr expr @ [WRITE]
  | Stmt.Assign (var, expr) -> compileExpr expr @ [ST var]
  | Stmt.Seq (x, y) -> compile x @ compile y

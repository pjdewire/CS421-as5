signature SEMANT =
sig
  type ir_code
  val transprog : Absyn.exp -> {exp: ir_code, ty: Types.ty}
end

structure Semant : SEMANT = 
struct

  structure A = Absyn
  structure E = Env
  structure S = Symbol
  structure T = Types
  val error = ErrorMsg.error
  type ir_code = unit (* not used for the time being *)

  
  (*** FILL IN DETAILS OF YOUR TYPE CHECKER PLEASE !!! ***)

  (*************************************************************************
   *                       UTILITY FUNCTIONS                               *
   *************************************************************************)

  (* checks whether an expression is of type int *)
  fun checkInt ({exp = _, ty = T.INT}, pos) = ()
    | checkInt ({exp = _, ty = _}, pos) = error pos "Must use type int"

  (* gives type returned by transexp on an exp *)
  fun transexpVal ({exp, ty}) = ty

  fun eqType (T.INT, T.INT, _) = true
    | eqType (T.STRING, T.STRING, _) = false
    | eqType (T.UNIT, T.UNIT, _) = false
    | eqType (T.RECORD(l1, u1), T.RECORD(l2, u2), _) = if u1 = u2 then true else
      false
    | eqType (T.RECORD(l1, u1), T.NIL, _) = true
    | eqType (T.NIL, T.RECORD(l1, u1), _) = true
    | eqType (T.ARRAY(t1, u1), T.ARRAY(t2, u2), _) = if u1 = u2 then true else false
    | eqType (t1, t2, _) = if t1 = t2 then true else false

  (* shortens int type returns *)
  fun intRet () = {exp=(), ty=T.INT}

  (* shortens string type returns *)
  fun stringRet () = {exp=(), ty=T.STRING}

  (* shortens string type returns *)
  fun nilRet () = {exp=(), ty=T.NIL}

  (* checks that the types are equal for Neq and Eq (can be ints, arrays or
     records *)
  fun checkNeq ({exp=_, ty=T.INT}, {exp=_, ty=T.INT}, pos, _) = (print "top"; 
    intRet())
    | checkNeq ({exp=_, ty=T.RECORD(l1, u1)}, {exp=_, ty=T.RECORD(l2, u2)}, 
                pos, _) = if u1 = u2 then intRet()
                          else (error pos 
                                "Cannot compare records of different types";
                                intRet())
    | checkNeq ({exp=_, ty=T.RECORD(l1, u1)}, {exp=_, ty=T.NIL}, pos, _) =
                intRet()
    | checkNeq ({exp=_, ty=T.NIL}, {exp=_, ty=T.RECORD(l1, u1)}, pos, _) =
                intRet()
    | checkNeq ({exp=_, ty=T.ARRAY(_, u1)}, {exp=_, ty=T.ARRAY(_, u2)},
                pos, _) = if u1 = u2 then intRet()
                          else (error pos
                                "Cannot compare arrays of different types";
                                intRet())
    | checkNeq ({exp=_, ty=_}, {exp=_, ty=_}, pos, tenv) = 
        (error pos "Cannot compare these types with <> or =";
         {exp=(), ty=T.INT})





 (**************************************************************************
  *                   TRANSLATING TYPE EXPRESSIONS                         *
  *                                                                        *
  *              transty : (E.tenv * A.ty) -> (T.ty * A.pos)               *
  *************************************************************************)
  fun transty (tenv, A.ArrayTy(id, pos)) = (* ... *) (T.UNIT, pos)
    | transty (tenv, _ (* other cases *)) = (* ... *) (T.UNIT, 0)

  (* ...... *)




 (**************************************************************************
  *                   TRANSLATING EXPRESSIONS                              *
  *                                                                        *
  *  transexp : (E.env * E.tenv) -> (A.exp -> {exp : ir_code, ty : T.ty})  *
  **************************************************************************)
  fun transexp (env, tenv) expr =
    let fun g (A.OpExp {left,oper=A.NeqOp,right,pos}) = 
              checkNeq(g left, g right, pos, tenv)

          | g (A.OpExp {left,oper=A.EqOp,right,pos}) =
              checkNeq(g left, g right, pos, tenv)

          | g (A.OpExp {left,oper,right,pos}) =
 		   (checkInt (g left, pos);
		    checkInt (g right, pos);
 		    {exp=(), ty=T.INT})

          | g (A.RecordExp {typ,fields,pos}) =
                   (* ... *) {exp=(), ty=T.RECORD ((* ? *) [], ref ())}

          | g (A.StringExp(_, _)) = stringRet()
          | g (A.IntExp(_)) = intRet()
          | g (A.NilExp) = nilRet()
          | g (A.LetExp{decs, body, pos}) = 
                let val (env', tenv') = transdecs (env, tenv, decs)
                in
                  transexp (env', tenv') body
                end

          | g _ (* other cases *) = {exp=(), ty=T.INT} 

        (* function dealing with "var", may be mutually recursive with g *)
        and h (A.SimpleVar (id,pos)) = (* ... *) {exp=(), ty=T.INT}
	  | h (A.FieldVar (v,id,pos)) = (* ... *) {exp=(), ty=T.INT}
	  | h (A.SubscriptVar (v,exp,pos)) = (* ... *) {exp=(), ty=T.INT}

     in g expr
    end

 (**************************************************************************
  *                   TRANSLATING DECLARATIONS                             *
  *                                                                        *
  *  transdec : (E.env * E.tenv * A.dec) -> (E.env * E.tenv)               *
  **************************************************************************)
  and transdec (env, tenv, A.VarDec{var={name, escape}, typ, init, pos}) = 
    let
      val expType = transexpVal(transexp (env, tenv) init)
    in
        (case typ of SOME((symbol, pos')) => 
                    (case S.look(tenv, symbol)
                     of NONE => (error pos ("undefined type " ^ S.name(symbol)); (* type not in table *)
                                 let val env' = S.enter(env, name, 
                                      E.VARentry{access=(), ty=expType})
                                 in
                                   (env', tenv)
                                 end)
                        | SOME(ty) => if expType = ty then
                          let
                            val env' = S.enter(env, name,
                                E.VARentry{access=(), ty=expType})
                          in
                            (env', tenv)
                          end
                                      else (* type in table but doesn't match *)
                                        (error pos "Initialization expression type not equal to constraint type";
                                        let val env' = S.enter(env, name,
                                             E.VARentry{access=(), ty=expType})
                                        in
                                          (env', tenv)
                                        end))
                  | NONE => if expType = T.NIL
                              then (error pos "NIL initializations must be constrained by a RECORD type";
                                let
                                  val env' = S.enter(env, name, 
                                      E.VARentry{access=(), ty=T.NIL})
                                in
                                  (env', tenv)
                                end) 
                            else let
                                  val env' = S.enter(env, name, 
                                      E.VARentry{access=(), ty=T.NIL})
                                in
                                  (env', tenv)
                                end)
    end
                  (*
           
          (error pos "NIL initializations must be constrained by RECORD type"; 
           let 
             val env' = S.enter(env, name, E.Varentry({access=(), ty=T.NIL}))
           in
             (env', tenv)
           end) 
         else let
                val env' = S.enter(env, name, E.VARentry{access=(), ty=typ})
              in
                (env', tenv)
              end;
              *)
    
    | transdec (env, tenv, A.FunctionDec(declist)) = (* ... *) (env, tenv)
    | transdec (env, tenv, A.TypeDec(declist)) = (* ... *) (env, tenv)


  (*** transdecs : (E.env * E.tenv * A.dec list) -> (E.env * E.tenv) ***)
  and transdecs (env,tenv,nil) = (env, tenv)
    | transdecs (env,tenv,dec::decs) =
	let val (env',tenv') = transdec (env,tenv,dec)
 	 in transdecs (env',tenv',decs)
	end

  (*** transprog : A.exp -> {exp : ir_code, ty : T.ty} ***)
  fun transprog prog = transexp (E.base_env, E.base_tenv) prog

end  (* structure Semant *)
  


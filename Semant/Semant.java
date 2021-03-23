package Semant;

import Absyn.ExpList;
import Absyn.SeqExp;
import ErrorMsg.ErrorMsg;
import Symbol.Table;
import java.util.Hashtable;
import Translate.Exp;
import Types.*;
//import Types.Type;

public class Semant {
  Env env;

  public Semant(ErrorMsg.ErrorMsg err) {
    this(new Env(err));
  }

  Semant(Env e) {
    env = e;  //do I need to make it this.env = e;
  }

  public void transProg(Absyn.Exp exp) {
    transExp(exp);
  }

  private void error(int pos, String msg) {
    env.errorMsg.error(pos, msg);   //do i need to make it this.env.errorMsg.error(pos, msg);
  }

  //static final Types.VOID   VOID   = new Types.VOID();   keeping types. to avoid confusion
  static final Types.VOID   VOID   = new VOID();
  static final Types.INT    INT    = new INT();
  static final Types.STRING STRING = new STRING();
  static final TypesNIL    NIL    = new NIL();

  private Exp checkInt(ExpTy et, int pos) {
    if (!INT.coerceTo(et.ty))
      error(pos, "integer required");
    return et.exp;
  }

  private Exp checkComparable(ExpTy et, int pos) //checks to see if it is a valid type
  {
  	Type a = et.ty.actual();
  	if ((!(a instanceof INT)) ||
  		(!(a instanceof STRING)) ||
  		(!(a instanceof NIL)) ||
  		(!(a instanceof RECORD)) ||
  		(!(a instanceof ARRAY)))
  	{
  		error(pos, "integer, string, nil, record, or array is required");
  	}
  	return et.exp;
  }

  private Exp checkOrderable(ExpTy et, int pos)
  {
  	Type a = et.ty.actual();
  	if((!(a instanceof INT)) ||
  		(!(a instanceof STRING)))
  	{
  		error(pos, "integer or string is required");
  	}
  	return et.exp;
  }

  ExpTy transExp(Absyn.Exp e) {
    ExpTy result;

    if (e == null)
      return new ExpTy(null, VOID);
    else if (e instanceof Absyn.OpExp)
      result = transExp((Absyn.OpExp)e);
    else if (e instanceof Absyn.LetExp)
      result = transExp((Absyn.LetExp)e);
    else throw new Error("Semant.transExp");
    e.type = result.ty;
    return result;
  }

  ExpTy transExp(Absyn.OpExp e) {
    ExpTy left = transExp(e.left);
    ExpTy right = transExp(e.right);

    switch (e.oper) {
    case Absyn.OpExp.PLUS:
      checkInt(left, e.left.pos);
      checkInt(right, e.right.pos);
      return new ExpTy(null, INT);
    default:
      throw new Error("unknown operator");
    }
  }

  ExpTy transExp(Absyn.LetExp e) {
    env.venv.beginScope();
    env.tenv.beginScope();
    for (Absyn.DecList d = e.decs; d != null; d = d.tail) {
      transDec(d.head);
    }
    ExpTy body = transExp(e.body);
    env.venv.endScope();
    env.tenv.endScope();
    return new ExpTy(null, body.ty);
  }

  Exp transDec(Absyn.Dec d) {
    if (d instanceof Absyn.VarDec)
      return transDec((Absyn.VarDec)d);
    throw new Error("Semant.transDec");
  }

  Exp transDec(Absyn.VarDec d) {
    // NOTE: THIS IMPLEMENTATION IS INCOMPLETE
    // It is here to show you the general form of the transDec methods
    ExpTy init = transExp(d.init);
    Type type;
    if (d.typ == null) {
      type = init.ty;
    } else {
      type = VOID;
      throw new Error("unimplemented");
    }
    d.entry = new VarEntry(type);
    env.venv.put(d.name, d.entry);
    return null;
  }
}


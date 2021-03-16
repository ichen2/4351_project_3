package Semant;

public class FunEntry extends Entry {
  public Types.RECORD formals;
  public Types.Type result;
  public boolean hasBody;
  FunEntry(Types.RECORD f, Types.Type r) {
    formals = f;
    result = r;
    hasBody =  true;
  }
  FunEntry(Types.RECORD f, Types.Type r, boolean b) {
    formals = f;
    result = r;
    hasBody =  b;
  }
}

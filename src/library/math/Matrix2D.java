package library.math;

//@ non_null_by_default
public class Matrix2D {
    public /*@ non_null @*/ Vectors2D row1 = new Vectors2D();
    public /*@ non_null @*/ Vectors2D row2 = new Vectors2D();

    /**
     * Default constructor matrix [(0,0),(0,0)] by default.
     */
    /*@ public normal_behavior
      @   ensures row1.isZero();
      @   ensures row2.isZero();
      @   ensures row1 != null;
      @   ensures row2 != null;
      @   pure
      @*/
    //@skipesc
    public Matrix2D() {
    }

    /**
     * Constructs and sets the matrix up to be a rotation matrix that stores the angle specified in the matrix.
     * @param radians The desired angle of the rotation matrix
     */
    //@skipesc
    //ver transpose
    public Matrix2D(double radians) {
        this.set(radians);
    }

    /**
     * Sets the matrix up to be a rotation matrix that stores the angle specified in the matrix.
     * @param radians The desired angle of the rotation matrix
     */
    /*@ public normal_behavior
      @   assigns row1.*,row2.*;
      @   requires !Double.isInfinite(radians);
      @   requires !Double.isNaN(radians);
      @   ensures row1.x == StrictMath.cos(radians);
      @   ensures row1.y == -StrictMath.sin(radians);
      @   ensures row2.x == StrictMath.sin(radians);
      @   ensures row2.y == StrictMath.cos(radians);
      @*/
    //ver transpose
    //@skipesc
    public void set(double radians) {
        double c = StrictMath.cos(radians);
        double s = StrictMath.sin(radians);

        row1.x = c;
        //@ assert row1.x == c;
        row1.y = -s;
        //@ assert row1.x == c;
        row2.x = s;
        //@ assert row1.x == c;
        row2.y = c;
        //@ assert row1.x == c;
    }

    /**
     * Sets current object matrix to be the same as the supplied parameters matrix.
     * @param m Matrix to set current object to
     */
    /*@ public normal_behavior
      @   requires row1.isValid() && row2.isValid();
      @   assigns row1.*,row2.*;
      @*/
    //Da mesma forma que transpose(), por algum motivo que não compreendo, a partir do momento
    //que ele faz row2. = m.row2.x, ele não consegue mais afirmar que row1.x e m.1row1.x são iguais
    //me ajuda.
    public void set(Matrix2D m) {
        row1.x = m.row1.x;
        row1.y = m.row1.y;
        row2.x = m.row2.x;
        row2.y = m.row2.y;
    }

    /*@ public normal_behavior
      @   requires row1.isValid() && row2.isValid();
      @*/
    //@skipesc
    //TODO: adicionar os ensures de igualdade, se o openjml não tiver bugado.
    public Matrix2D transpose() {
        Matrix2D mat = new Matrix2D();
        mat.row1.x = row1.x;
        //@ assert mat.row1.x == row1.x;
        mat.row1.y = row2.x;
        //@ assert mat.row1.x == row1.x;
        mat.row2.x = row1.y;
        //Por algum motivo que desconheço, o OpenJML simplesmente tem um derrame e acha que
        //mat.row1.x != row.x a partir daqui.
        //?????????????????????????????????????????
        mat.row2.y = row2.y;
        return mat;
    }

    /*@ public normal_behavior
      @   requires v != null;
      @   requires v != row1;
      @   requires v != row2;
      @   assignable v.x, v.y;
      @   requires !Double.isInfinite(v.x*row1.x + v.y*row1.y);
      @   requires !Double.isInfinite(v.x*row2.x + v.y*row2.y);
      @   requires !Double.isNaN(v.x*row1.x + v.y*row1.y);
      @   requires !Double.isNaN(v.x*row2.x + v.y*row2.y);
      @   ensures \result.x == \old(row1.x * v.x + row1.y * v.y);
      @   ensures \result.y == \old(row2.x * v.x + row2.y * v.y);
      @   ensures \result == v;
      @*/
    //@skipesc
    public Vectors2D mul(Vectors2D v) {
        double x = v.x;
        double y = v.y;
        v.x = row1.x * x + row1.y * y;
        v.y = row2.x * x + row2.y * y;
        return v;
    }


    /*@ public normal_behavior
      @   assigns out.x, out.y;
      @   requires v != null;
      @   requires out != null;
      @
      @   requires out != row1;
      @   requires out != row2;
      @   requires v != out;
      @
      @   requires !Double.isInfinite((row1.x * v.x) + (row1.y * v.y));
      @   requires !Double.isInfinite((row2.x * v.x) + (row2.y * v.y));
      @   requires !Double.isNaN((row1.x * v.x) + (row1.y * v.y));
      @   requires !Double.isNaN((row2.x * v.x) + (row2.y * v.y));
      @
      @   ensures out.x == (row1.x * v.x) + (row1.y * v.y);
      @   ensures \result.y == (row2.x * v.x) + (row2.y * v.y);
      @   ensures \result == out;
      @*/
    public Vectors2D mul(Vectors2D v, Vectors2D out) {
        out.x = row1.x * v.x + row1.y * v.y;
        out.y = row2.x * v.x + row2.y * v.y;
        return out;
    }

    //@skipesc
    public static void main(String[] args) {
        Vectors2D test = new Vectors2D(5, 0);
        Matrix2D m = new Matrix2D();
        m.set(0.5);
        m.mul(test);
        System.out.println(test);
    }

    //@skipesc
    @Override
    public String toString() {
        return row1.x + " : " + row1.y + "\n" + row2.x + " : " + row2.y;
    }
}

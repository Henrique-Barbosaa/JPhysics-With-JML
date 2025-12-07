package library.math;

/**
 * 2D Vectors class
 */
public class Vectors2D {
    public double x;
    public double y;

    /**
     * Default constructor - x/y initialised to zero.
     */
    /*@ public normal_behavior
      @   ensures this != null;
      @   ensures this.x == 0;
      @   ensures this.y == 0;
      @ pure
      @*/
    //@skipesc
    public Vectors2D() {
        this.x = 0;
        this.y = 0;
    }

    /**
     * Constructor.
     *
     * @param x Sets x value.
     * @param y Sets y value.
     */
    /*@ public normal_behavior
      @   ensures this != null;
      @   ensures this.x == x;
      @   ensures this.y == y;
      @ pure
      @*/
    //@skipesc
    public Vectors2D(double x, double y) {
        this.x = x;
        this.y = y;
    }

    /**
     * Copy constructor.
     *
     * @param vector Vector to copy.
     */
    /*@ public normal_behavior
      @   requires vector != null;
      @   ensures this != null;
      @   ensures this.x == vector.x;
      @   ensures this.y == vector.y;
      @ pure
      @*/
    //@skipesc
    public Vectors2D(Vectors2D vector) {
        this.x = vector.x;
        this.y = vector.y;
    }

    /**
     * Constructs a normalised direction vector.
     *
     * @param direction Direction in radians.
     */
    /*@ public normal_behavior
      @   requires Double.isFinite(direction);
      @   ensures this != null;
      @   ensures -1 <= this.x <= 1;
      @   ensures -1 <= this.y <= 1;
      @ pure
      @*/
    //@skipesc
    public Vectors2D(double direction) {
        this.x = Math.cos(direction);
        this.y = Math.sin(direction);
    }

    /**
     * Sets a vector to equal an x/y value and returns this.
     *
     * @param x x value.
     * @param y y value.
     * @return The current instance vector.
     */
    /*@ public normal_behavior
      @   assignable this.x, this.y;
      @   ensures this.x == x;
      @   ensures this.y == y;
      @   ensures \result == this;
      @*/
    //@skipesc
    public Vectors2D set(double x, double y) {
        this.x = x;
        this.y = y;
        return this;
    }

    /**
     * Sets a vector to another vector and returns this.
     *
     * @param v1 Vector to set x/y values to.
     * @return The current instance vector.
     */
    /*@ public normal_behavior
      @   requires v1 != null;
      @   assignable this.x, this.y;
      @   ensures this.x == v1.x;
      @   ensures this.y == v1.y;
      @   ensures \result == this;
      @*/
    //@skipesc
    public Vectors2D set(Vectors2D v1) {
        this.x = v1.x;
        this.y = v1.y;
        return this;
    }


    /**
     * Copy method to return a new copy of the current instance vector.
     *
     * @return A new Vectors2D object.
     */
    /*@ public normal_behavior
      @   ensures \result instanceof Vectors2D;
      @   ensures \result.x == this.x;
      @   ensures \result.y == this.y;
      @   spec_pure
      @*/
    //@skipesc
    public Vectors2D copy() {
        return new Vectors2D(this.x, this.y);
    }

    /**
     * Negates the current instance vector and return this.
     *
     * @return Return the negative form of the instance vector.
     */
    /*@ public normal_behavior
      @   assignable x, y;
      @   ensures this.x == -\old(x);
      @   ensures this.y == -\old(y);
      @   ensures \result == this;
      @*/
    //@skipesc
    public Vectors2D negative() {
        this.x = -x;
        this.y = -y;
        return this;
    }

    /**
     * Negates the current instance vector and return this.
     *
     * @return Returns a new negative vector of the current instance vector.
     */
    /*@ public normal_behavior
      @   ensures \result instanceof Vectors2D;
      @   ensures \result.x == -this.x;
      @   ensures \result.y == -this.y;
      @   spec_pure
      @*/
    //@skipesc
    public Vectors2D negativeVec() {
        return new Vectors2D(-x, -y);
    }

    /**
     * Adds a vector to the current instance and return this.
     *
     * @param v Vector to add.
     * @return Returns the current instance vector.
     */
    /*@ public normal_behavior
      @   assigns x,y;
      @   requires v != null;
      @   requires Double.isFinite(v.x);
      @   requires Double.isFinite(v.y);
      @   ensures \result.x == \old(x) + \old(v.x);
      @   ensures \result.y == \old(y) + \old(v.y);
      @   ensures \result == this;
      @*/
    //@skipesc
    public Vectors2D add(Vectors2D v) {
        this.x = x + v.x;
        this.y = y + v.y;
        return this;
    }

    /**
     * Adds a vector and the current instance vector together and returns a new vector of them added together.
     *
     * @param v Vector to add.
     * @return Returns a new Vectors2D of the sum of the addition of the two vectors.
     */
    /*@ public normal_behavior
      @   requires v != null;
      @   requires Double.isFinite(v.x);
      @   requires Double.isFinite(v.y);
      @   ensures \result instanceof Vectors2D;
      @   ensures \result.x == this.x + v.x;
      @   ensures \result.y == this.y + v.y;
      @ spec_pure
      @*/
    //@skipesc
    public Vectors2D addi(Vectors2D v) {
        return new Vectors2D(x + v.x, y + v.y);
    }

    /**
     * Generates a normal of a vector. Normal facing to the right clock wise 90 degrees.
     *
     * @return A normal of the current instance vector.
     */
    /*@ public normal_behavior
      @   ensures \result.x == -this.y;
      @   ensures \result.y == this.x;
      @   ensures \result instanceof Vectors2D;
      @   spec_pure
      @*/
    //@skipesc
    public Vectors2D normal() {
        return new Vectors2D(-y, x);
    }

    /**
     * Normalizes the current instance vector to length 1 and returns this.
     *
     * @return Returns the normalized version of the current instance vector.
     */
    /*@ public normal_behavior
      @   assigns x, y;
      @   requires x != 0 || y != 0;
      @   requires Double.POSITIVE_INFINITY>x*x+y*y;
      @   requires_redundantly x*x+y*y>0;
      @   ensures \result == this;
      @ also
      @ public normal_behavior
      @   assigns x, y;
      @   requires this.x == 0;
      @   requires this.y == 0;
      @   requires Math.isPositiveZero(x*x + y*y);
      @   ensures this.x == \old(x);
      @   ensures this.y == \old(y);
      @   ensures \result == this;
      @*/
    //@skipesc
    public Vectors2D normalize() {
        double d = Math.sqrt(x * x + y * y);
        if (d == 0) {
            d = 1;
        }
        this.x /= d;
        this.y /= d;
        return this;
    }

    /**
     * Finds the normalised version of a vector and returns a new vector of it.
     *
     * @return A normalized vector of the current instance vector.
     */
    /*@ public normal_behavior
      @   requires x != 0 || y != 0;
      @   requires Double.POSITIVE_INFINITY>x*x+y*y;
      @   requires_redundantly x*x+y*y>0;
      @   requires_redundantly length()>0.0;
      @   ensures x==\old(x);
      @   ensures y==\old(y);
      @ also
      @ public normal_behavior
      @   requires !(x!=0||y!=0);
      @   requires Math.isPositiveZero(x*x + y*y);
      @   ensures \result.x == \old(x);
      @   ensures \result.y == \old(y);
      @ spec_pure
      @*/
    //@skipesc
    //TODO: ajeitar
    public Vectors2D getNormalized() {
        double d = Math.sqrt(x * x + y * y);
        if (d == 0) {
            d = 1;
        }
        return new Vectors2D(x / d, y / d);
    }

    /**
     * Finds the distance between two vectors.
     *
     * @param v Vector to find distance from.
     * @return Returns distance from vector v to the current instance vector.
     */
    /*@ public normal_behavior
      @   requires v != null;
      @   requires Double.POSITIVE_INFINITY>(x-v.x)*(x-v.x)+(y-v.y)*(y-v.y)>0;
      @   ensures \result == StrictMath.sqrt((this.x-v.x)*(this.x-v.x)+(this.y-v.y)*(this.y-v.y));
      @   pure
      @*/
    //@skipesc
    public double distance(Vectors2D v) {
        double dx = this.x - v.x;
        double dy = this.y - v.y;
        return StrictMath.sqrt(dx * dx + dy * dy);
    }

    /**
     * Subtract a vector from the current instance vector.
     *
     * @param v1 Vector to subtract.
     * @return Returns a new Vectors2D with the subtracted vector applied
     */
    /*@ public normal_behavior
      @   requires v1 != null;
      @   requires Double.isFinite(v1.x);
      @   requires Double.isFinite(v1.y);
      @   ensures \result.x == this.x-v1.x;
      @   ensures \result.y == this.y-v1.y;
      @   spec_pure
      @*/
    //@skipesc
    public Vectors2D subtract(Vectors2D v1) {
        return new Vectors2D(this.x - v1.x, this.y - v1.y);
    }

    /**
     * Finds cross product between two vectors.
     *
     * @param v1 Other vector to apply cross product to
     * @return double
     */
    /*@ public normal_behavior
      @   requires v1 != null;
      @   requires Double.isFinite(v1.x);
      @   requires Double.isFinite(v1.y);
      @   ensures \result == this.x*v1.y-this.y*v1.x;
      @   pure
      @*/
    //@skipesc
    public double crossProduct(Vectors2D v1) {
        return this.x * v1.y - this.y * v1.x;
    }

    /*@ public normal_behavior
      @   requires Double.isFinite(a);
      @   ensures \result == this.normal().scalar(a);
      @*/
    //@skipesc
    public Vectors2D crossProduct(double a) {
        return this.normal().scalar(a);
    }

    /*@ public normal_behavior
      @   requires Double.isFinite(a);
      @   ensures \result.x == this.x*a;
      @   ensures \result.y == this.y*a;
      @   spec_pure
      @*/
    //@skipesc
    public Vectors2D scalar(double a) {
        return new Vectors2D(x * a, y * a);
    }

    /**
     * Finds dotproduct between two vectors.
     *
     * @param v1 Other vector to apply dotproduct to.
     * @return double
     */
    /*@ public normal_behavior
      @   requires v1 != null;
      @   requires Double.isFinite(v1.x);
      @   requires Double.isFinite(v1.y);
      @   ensures \result == this.x*v1.x+this.y*v1.y;
      @   pure
      @*/
    //@skipesc
    public double dotProduct(Vectors2D v1) {
        return v1.x * this.x + v1.y * this.y;
    }

    /**
     * Gets the length of instance vector.
     *
     * @return double
     */
        /*@ public normal_behavior
          @   requires Double.POSITIVE_INFINITY>x*x+y*y>0;
          @   ensures \result >= 0;
          @   ensures this.isZero() == false;
          @   ensures_redundantly x!=0||y!=0;
          @ also
          @   requires Math.isPositiveZero(x*x+y*y);
          @   ensures Math.isPositiveZero(\result);
          @ pure
          @*/
    //@skipesc
    public double length() {
            return Math.sqrt(x * x + y * y);

    }

    /**
     * Static method for any cross product, same as
     * {@link #cross(double, Vectors2D)}
     *
     * @param s double.
     * @param a Vectors2D.
     * @return Cross product scalar result.
     */
    /*@ public normal_behavior
      @   requires a != null;
      @   requires Double.isFinite(a.x);
      @   requires Double.isFinite(a.y);
      @   requires Double.isFinite(s);
      @   ensures \result.x == s*a.y;
      @   ensures \result.y == -s*a.x;
      @*/
    //@skipesc
    public static Vectors2D cross(Vectors2D a, double s) {
        return new Vectors2D(s * a.y, -s * a.x);
    }

    /**
     * Finds the cross product of a scalar and a vector. Produces a scalar in 2D.
     *
     * @param s double.
     * @param a Vectors2D.
     * @return Cross product scalar result.
     */
    /*@ public normal_behavior
      @   requires a != null;
      @   requires Double.isFinite(a.x);
      @   requires Double.isFinite(a.y);
      @   requires Double.isFinite(s);
      @   ensures \result.x == -s*a.y;
      @   ensures \result.y == s*a.x;
      @*/
    //@skipesc
    public static Vectors2D cross(double s, Vectors2D a) {
        return new Vectors2D(-s * a.y, s * a.x);
    }

    /**
     * Checks to see if a vector has valid values set for x and y.
     *
     * @return boolean value whether a vector is valid or not.
     */
    /*@ public normal_behavior
      @   requires !(Double.isNaN(x) || Double.isInfinite(x) || Double.isNaN(y) || Double.isInfinite(y));
      @   ensures \result == true;
      @ also
      @   requires (Double.isNaN(x) || Double.isInfinite(x) || Double.isNaN(y) || Double.isInfinite(y));
      @   ensures \result == false;
      @   pure
      @*/

    //por algum motivo que eu desconheço usar o que tá escrito no return dá erro, e usar Double.isFinite()
    //também, mas se eu jogar a lei de demorgan no return ele começa a funcionar
    //laerte eu não entendi
    //@skipesc
    public final boolean isValid() {
        return !Double.isNaN(x) && !Double.isInfinite(x) && !Double.isNaN(y) && !Double.isInfinite(y);
    }

    /**
     * Checks to see if a vector is set to (0,0).
     *
     * @return boolean value whether the vector is set to (0,0).
     */
    /*@ public normal_behavior
      @   requires x == 0 && y == 0;
      @   ensures \result == true;
      @ also
      @   requires x != 0 || y != 0;
      @   ensures \result == false;
      @   pure
      @*/
    //@skipesc
    public boolean isZero() {
        return Math.abs(this.x) == 0 && Math.abs(this.y) == 0;
    }

    /**
     * Generates an array of length n with zero initialised vectors.
     *
     * @param n Length of array.
     * @return A Vectors2D array of zero initialised vectors.
     */
    /*@ public normal_behavior
      @   requires Integer.MAX_VALUE > n > 0;
      @   ensures \result.length == n;
      @*/

    //TODO: Ajeitar essa degraça
    //Eu não sei porque "@ maintaining \forall int k; 0<=k<\count; array[k].isZero();" (ou a mesma coisa
    //substituindo o ".isZero()" por " != null" simplesmente não funciona mas sem isso simplesmente
    //não dá pra colocar que ele inicializa tudo com 0,0.
    //@skipesc
    public static Vectors2D[] createArray(int n) {
        Vectors2D[] array = new Vectors2D[n];
        /*@ maintaining 0 <= \count <= array.length;
          @ loop_invariant (\forall int j; 0<=j<\count; array[j] != null);
          @ loop_writes array[*];
          @ decreases array.length - \count;
          @*/
        for (Vectors2D v : array) {
            v = new Vectors2D();
        }
        return array;
    }
    //@skipesc
    @Override
    public String toString() {
        return this.x + " : " + this.y;
    }
}

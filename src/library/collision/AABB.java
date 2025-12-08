package library.collision;

import library.dynamics.Body;
import library.math.Vectors2D;

/**
 * Axis aligned bounding box volume class. Allows the creation of bounding volumes to make broad phase collision check possible and easy to do.
 */
//@ nullable_by_default
public class AABB {
    /**
     * Lower left vertex of bounding box.
     */
    private /*@ spec_public non_null @*/ Vectors2D min;
    /**
     * Top right vertex of bounding box.
     */
    private /*@ spec_public non_null @*/ Vectors2D max;

    /*@ public initially max != null; @*/
    /*@ public initially min != null; @*/

    //@ public invariant min != null;
    //@ public invariant max != null;
    //@ public invariant min != max;

    /**
     * Constructor to generate an AABB given a minimum and maximum bound in the form of two vectors.
     *
     * @param min Lower bound of AABB vertex.
     * @param max Higher bound of AABB vertex.
     */
    /*@ public normal_behavior
      @   requires min != null;
      @   requires max != null;
      @   requires min != max;
      @   ensures this.min.x == min.x && this.min.y == min.y;
      @   ensures this.max.x == max.x && this.max.y == max.y;
      @   pure
      @*/
    public AABB(Vectors2D min, Vectors2D max) {
        this.min = min.copy();
        this.max = max.copy();
    }

    /**
     * Default constructor generating an AABB with (0,0) upper and lower bounds.
     */
    /*@ public normal_behavior
      @   pure
      @*/
    public AABB() {
        this.min = new Vectors2D();
        this.max = new Vectors2D();
    }

    /**
     * Sets the current objects bounds equal to that of the passed AABB argument.
     *
     * @param aabb An AABB bounding box.
     */
    /*@ public normal_behavior
      @   requires aabb != null;
      @   requires aabb.min != null;
      @   requires aabb.max != null;
      @   assignable min.x, min.y, max.x, max.y;
      @   ensures this.min.x == \old(aabb.min.x) && this.min.y == \old(aabb.min.y);
      @   ensures this.max.x == \old(aabb.max.x) && this.max.y == \old(aabb.max.y);
      @*/
    public final void set(final AABB aabb) {
        double newMinX = aabb.min.x;
        double newMinY = aabb.min.y;
        double newMaxX = aabb.max.x;
        double newMaxY = aabb.max.y;

        min.x = newMinX;
        min.y = newMinY;
        max.x = newMaxX;
        max.y = newMaxY;
    }

    /**
     * Getter for min variable for lower bound vertex.
     *
     * @return AABB min
     */
    /*@ public normal_behavior
      @   ensures \result == this.min;
      @ pure
      @*/
    public Vectors2D getMin() {
        return min;
    }

    /**
     * Getter for max variable for upper bound vertex.
     *
     * @return AABB max
     */
    /*@ public normal_behavior
      @   ensures \result == this.max;
      @ pure
      @*/
    public Vectors2D getMax() {
        return max;
    }

    /**
     * Method to check if an AABB is valid.
     * Makes sure the bounding volume is not; a point, has order of vertex's backwards and valid values have been used for the bounds.
     *
     * @return boolean value of the validity of the AABB.
     */
    /*@ public normal_behavior
      @   requires max.x - min.x < 0;
      @   requires max.y - min.y < 0;
      @   ensures \result == false;
      @ also
      @   requires max.x - min.x >= 0;
      @   requires max.y - min.y >= 0;
      @   ensures \result == (min.isValid() && max.isValid());
      @ pure
      @*/
    public final boolean isValid() {
        if (max.x - min.x < 0) {
            return false;
        }
        if (max.y - min.y < 0) {
            return false;
        }
        return min.isValid() && max.isValid();
    }

    /**
     * Method to check if a point resides inside an AABB in object space.
     *
     * @param point A point to check if its inside the AABB's object space. Point needs to also be in object space.
     * @return Boolean value whether or not the point lies inside the AABB bounds.
     */
    /*@ public normal_behavior
      @   requires point != null;
      @   ensures \result == (point.x <= this.max.x && point.x >= this.min.x && 
      @                       point.y >= this.max.y && point.y <= this.min.y);
      @ pure
      @*/
    public boolean AABBOverLap(Vectors2D point) {
        double x = point.x;
        double y = point.y;
        return x <= this.getMax().x && x >= this.getMin().x && y >= this.getMax().y && y <= this.getMin().y;
    }

    /**
     * Method to add offset to the AABB's bounds. Can be useful to convert from object to world space .
     *
     * @param offset A vector to apply to the min and max vectors to translate the bounds and therefore AABB to desired position.
     */
    /*@ public normal_behavior
      @   requires offset != null;
      @   requires offset != min;
      @   requires offset != max;
      @   requires !Double.isInfinite(min.x + offset.x);
      @   requires !Double.isInfinite(min.y + offset.y);
      @   requires !Double.isInfinite(max.x + offset.x);
      @   requires !Double.isInfinite(max.y + offset.y);
      @   requires !Double.isNaN(min.x + offset.x);
      @   requires !Double.isNaN(min.y + offset.y);
      @   requires !Double.isNaN(max.x + offset.x);
      @   requires !Double.isNaN(max.y + offset.y);
      @   requires !Double.isFinite(offset.x) && !Double.isFinite(offset.y);
      @   requires !Double.isFinite(min.x + offset.x) && !Double.isFinite(min.y + offset.y);
      @   requires !Double.isFinite(max.x + offset.x) && !Double.isFinite(max.y + offset.y);
      @   assignable min.x, min.y, max.x, max.y;
      @
      @   ensures this.min.x == \old(this.min.x + offset.x);
      @   ensures this.min.y == \old(this.min.y + offset.y);
      @   ensures this.max.x == \old(this.max.x + offset.x);
      @   ensures this.max.y == \old(this.max.y + offset.y);
      @*/
    public void addOffset(Vectors2D offset) {
        this.min.add(offset);
        this.max.add(offset);
    }

    /*@ also public normal_behavior
      @   ensures \result != null;
      @   ensures \result instanceof String;
      @   pure
      @*/
    //@ skipesc
    @Override
    public final String toString() {
        return "AABB[" + min + " . " + max + "]";
    }

    /**
     * Copy method to return a new AABB that's the same as the current object.
     *
     * @return New AABB that's the same as the current object.
     */
    /*@ public normal_behavior
      @   ensures \result != null;
      @   ensures \result.min.x == this.min.x && \result.min.y == this.min.y;
      @   ensures \result.max.x == this.max.x && \result.max.y == this.max.y;
      @   ensures \fresh(\result);
      @ pure
      @*/
    public AABB copy() {
        return new AABB(this.min, this.max);
    }

    /**
     * Checks whether two body's AABB's overlap in world space.
     *
     * @param A First body to evaluate.
     * @param B Second body to evaluate.
     * @return Boolean value of whether the two bodies AABB's overlap in world space.
     */
    /*@ public normal_behavior
      @   requires A != null && B != null;
      @
      @   requires A.aabb != null && A.position != null;
      @   requires B.aabb != null && B.position != null;
      @
      @   requires !Double.isFinite(A.position.x) && !Double.isFinite(A.position.y);
      @   requires !Double.isFinite(B.position.x) && !Double.isFinite(B.position.y);
      @
      @   requires A.aabb.min != null && A.aabb.max != null;
      @   requires A.aabb.min != A.aabb.max;
      @   
      @   requires B.aabb.min != null && B.aabb.max != null;
      @   requires B.aabb.min != B.aabb.max;
      @
      @   requires Double.isFinite(A.aabb.min.x + A.position.x);
      @   requires Double.isFinite(A.aabb.min.y + A.position.y);
      @   requires Double.isFinite(A.aabb.max.x + A.position.x);
      @   requires Double.isFinite(A.aabb.max.y + A.position.y);
      @
      @   requires Double.isFinite(B.aabb.min.x + B.position.x);
      @   requires Double.isFinite(B.aabb.min.y + B.position.y);
      @   requires Double.isFinite(B.aabb.max.x + B.position.x);
      @   requires Double.isFinite(B.aabb.max.y + B.position.y);
      @
      @*/
    public static boolean AABBOverLap(Body A, Body B) {
        AABB aCopy = A.aabb.copy();
        AABB bCopy = B.aabb.copy();

        //@ assume A.position != aCopy.min && A.position != aCopy.max;
        //@ assume B.position != bCopy.min && B.position != bCopy.max;

        aCopy.addOffset(A.position);
        bCopy.addOffset(B.position);

        return AABB.AABBOverLap(aCopy, bCopy);
    }

    /**
     * Method to check if two AABB's overlap. Can be seen as world space.
     *
     * @param a First AABB to evaluate.
     * @param b Second AABB to evaluate.
     * @return Boolean value of whether two bounds of the AABB's overlap.
     */
    /*@ public normal_behavior
      @   requires a != null;
      @   requires b != null;
      @   ensures \result == (a.min.x <= b.max.x &&
      @                       a.max.x >= b.min.x &&
      @                       a.min.y <= b.max.y &&
      @                       a.max.y >= b.min.y);
      @ pure
      @*/
    public static boolean AABBOverLap(AABB a, AABB b) {
        return a.min.x <= b.max.x &&
                a.max.x >= b.min.x &&
                a.min.y <= b.max.y &&
                a.max.y >= b.min.y;
    }
}

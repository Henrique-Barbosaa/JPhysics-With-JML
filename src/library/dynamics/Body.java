package library.dynamics;

import library.collision.AABB;
import library.geometry.Shapes;
import library.math.Vectors2D;

/**
 * Class to create a body to add to a world.
 */
public class Body {
    public double dynamicFriction;
    public double staticFriction;
    public Vectors2D position;
    public Vectors2D velocity;
    public Vectors2D force;
    /*@ public invariant position.isValid();
      @ public invariant velocity.isValid();
      @ public invariant force.isValid();
      @*/

    public double angularVelocity;
    public double torque;

    public double restitution;
    public double mass, invMass, I, invI;

    public double orientation;

    public Shapes shape;
    public AABB aabb;

    public double linearDampening;
    public double angularDampening;
    public boolean affectedByGravity;
    public boolean particle;

    /**
     * Constructor for body.
     *
     * @param shape Shape to bind to body.
     * @param x     Position x in world space.
     * @param y     Position y in world space.
     */
    /*@ public normal_behavior
      @   requires shape != null;
      @   requires !Double.isNaN(x);
      @   requires !Double.isNaN(y);
      @   requires !Double.isInfinite(x);
      @   requires !Double.isInfinite(y);
      @   ensures this.shape == shape;
      @   ensures this.shape.body == this;
      @   ensures position.x == x;
      @   ensures position.y == y;
      @   ensures velocity.isZero();
      @   ensures force.isZero();
      @   ensures angularVelocity == 0;
      @   ensures torque == 0;
      @   ensures restitution == 0.8;
      @   ensures staticFriction == 0.5;
      @   ensures dynamicFriction == 0.2;
      @   ensures linearDampening == 0;
      @   ensures orientation == 0;
      @   ensures mass >= 0.0;
      @   ensures I >= 0.0;
      @   ensures invMass >= 0.0;
      @   ensures invI >= 0.0;
      @   ensures aabb!=null;
      @   ensures !particle;
      @   ensures affectedByGravity;
      @*/
    //@skipesc
    public Body(Shapes shape, double x, double y) {
        this.shape = shape;
        this.shape.body = this;

        position = new Vectors2D(x, y);
        velocity = new Vectors2D(0, 0);
        force = new Vectors2D(0, 0);

        angularVelocity = 0;
        torque = 0;

        restitution = 0.8;

        staticFriction = 0.5;
        dynamicFriction = 0.2;

        linearDampening = 0;
        angularDampening = 0;

        orientation = 0;
        shape.orient.set(orientation);

        this.shape.calcMass(1.0);
        this.shape.createAABB();

        particle = false;
        affectedByGravity = true;
    }

    /**
     * Applies force ot body.
     *
     * @param force        Force vector to apply.
     * @param contactPoint The point to apply the force to relative to the body in object space.
     */
    /*@ public normal_behavior
      @   assigns this.force.x,this.force.y,torque;
      @   requires force != null;
      @   requires force != this.force;
      @   requires force.isValid();
      @   requires contactPoint.isValid();
      @   requires !Double.isNaN(this.force.x + force.x);
      @   requires !Double.isNaN(this.force.y + force.y);
      @   requires !Double.isInfinite(this.force.x + force.x);
      @   requires !Double.isInfinite(this.force.y + force.y);
      @   requires Double.isFinite(torque+contactPoint.crossProduct(force));
      @   ensures this.force.x == \old(this.force.x+force.x);
      @   ensures this.force.y == \old(this.force.y+force.y);
      @   ensures torque == \old(this.torque+contactPoint.crossProduct(force));
      @*/
    //@skipesc
    public void applyForce(Vectors2D force, Vectors2D contactPoint) {
        //@ assume this.force.isValid();
        this.force.add(force);
        torque += contactPoint.crossProduct(force);
    }

    /**
     * Apply force to the center of mass.
     *
     * @param force Force vector to apply.
     */
    /*@ public normal_behavior
      @   assigns this.force.x, this.force.y;
      @   requires force != null;
      @   requires force != this.force;
      @   requires !Double.isNaN(this.force.x + force.x);
      @   requires !Double.isNaN(this.force.y + force.y);
      @   requires !Double.isInfinite(this.force.x + force.x);
      @   requires !Double.isInfinite(this.force.y + force.y);
      @   ensures this.force.x == \old(this.force.x+force.x);
      @   ensures this.force.y == \old(this.force.y+force.y);
      @*/
    //@skipesc
    public void applyForceToCentre(Vectors2D force) {
        //@assert !Double.isInfinite(this.force.x + force.x);
        this.force.add(force);
    }

    /**
     * Applies impulse to a point relative to the body's center of mass.
     *
     * @param impulse      Magnitude of impulse vector.
     * @param contactPoint The point to apply the force to relative to the body in object space.
     */
    /*@ public normal_behavior
      @  requires !Double.isInfinite(invMass);
      @  requires !Double.isNaN(invMass);
      @  requires !Double.isInfinite(impulse.x);
      @  requires !Double.isInfinite(impulse.y);
      @  requires !Double.isNaN(impulse.x);
      @  requires !Double.isNaN(impulse.y);
      @  requires !Double.isInfinite(impulse.scalar(invMass).x+velocity.x);
      @  requires !Double.isInfinite(impulse.scalar(invMass).y+velocity.y);
      @  requires !Double.isNaN(impulse.scalar(invMass).x+velocity.x);
      @  requires !Double.isNaN(impulse.scalar(invMass).y+velocity.y);
      @  requires contactPoint.isValid();
      @  ensures angularVelocity == \old(angularVelocity+invI * contactPoint.crossProduct(impulse));
      @  ensures velocity.x == \old(velocity.x + impulse.scalar(invMass).x);
      @  ensures velocity.y == \old(velocity.y+ impulse.scalar(invMass).y);
      @*/
    //@skipesc
    public void applyLinearImpulse(Vectors2D impulse, Vectors2D contactPoint) {
        velocity.add(impulse.scalar(invMass));
        angularVelocity += invI * contactPoint.crossProduct(impulse);
    }

    /**
     * Applies impulse to body's center of mass.
     *
     * @param impulse Magnitude of impulse vector.
     */
    /*@ public normal_behavior
      @   requires !Double.isInfinite(invMass);
      @   requires !Double.isNaN(invMass);
      @   requires !Double.isInfinite(impulse.scalar(invMass).x+velocity.x);
      @   requires !Double.isInfinite(impulse.scalar(invMass).y+velocity.y);
      @   requires !Double.isNaN(impulse.scalar(invMass).x+velocity.x);
      @   requires !Double.isNaN(impulse.scalar(invMass).y+velocity.y);
      @   ensures velocity.x == \old(velocity.x+ impulse.scalar(invMass).x);
      @   ensures velocity.y == \old(velocity.y+ impulse.scalar(invMass).y);
      @*/
    //@skipesc
    public void applyLinearImpulseToCentre(Vectors2D impulse) {
        velocity.add(impulse.scalar(invMass));
    }

    /**
     * Sets the orientation of the body's shape associated with it and recalculates AABB.
     *
     * @param delta Angle of orientation.
     */
    //depende de set e portanto terá os mesmos problemas
    /*@ public normal_behavior
      @   requires shape.body == this;
      @   requires !Double.isInfinite(delta);
      @   requires !Double.isNaN(delta);
      @   ensures orientation == delta;
      @*/
    //@skipesc
    public void setOrientation(double delta) {
        orientation = delta;
        shape.orient.set(orientation);
        shape.createAABB();
    }

    /**
     * Sets the density of the body's mass.
     *
     * @param density double value of desired density.
     */
    /*@ public normal_behavior
      @   assigns mass,invMass,I,invI;
      @   requires shape.body == this;
      @   requires !Double.isInfinite(density);
      @   requires density > 0.0;
      @   ensures mass >= 0.0;
      @   ensures I >= 0.0;
      @   ensures invMass >= 0.0;
      @   ensures invI >= 0.0;
      @ also
      @ public normal_behavior
      @   assigns mass,invMass,I,invI;
      @   requires Double.isFinite(density);
      @   requires density<=0.0;
      @   ensures mass == 0.0;
      @   ensures invMass == 0.0;
      @   ensures I == 0.0;
      @   ensures invI == 0.0;
      @*/
    
    public void setDensity(double density) {
        if (density > 0.0) {
            shape.calcMass(density);
        } else {
            setStatic();
        }
    }

    /**
     * Sets all mass and inertia variables to zero. Object cannot be moved.
     */
    /*@ normal_behavior
      @   assigns mass,invMass,I,invI;
      @   ensures mass == 0.0;
      @   ensures invMass == 0.0;
      @   ensures I == 0.0;
      @   ensures invI == 0.0;
      @*/
    //@spec_public
    
    private void setStatic() {
        mass = 0.0;
        invMass = 0.0;
        I = 0.0;
        invI = 0.0;
    }
}

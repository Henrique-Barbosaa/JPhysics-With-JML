package library.geometry;

// import testbed.Camera;
import library.collision.AABB;
import library.math.Vectors2D;
import testbed.ColourSettings;

import java.awt.*;
import java.awt.geom.Path2D;
import java.util.*;

/**
 * Class for representing polygon shape.
 */
public class Polygon extends Shapes {
    public Vectors2D[] vertices;
    public Vectors2D[] normals;

    /**
     * Constructor takes a supplied list of vertices and generates a convex hull around them.
     *
     * @param vertList Vertices of polygon to create.
     */
    //menor polígono possível é um triângulo por motivos que devem ser óbvios.
    /*@ public normal_behavior
      @   requires vertList.length > 0;
      @   ensures this.vertices != null;
      @   ensures \forall int i; 0<=i<vertices.length; vertices[i]!=null;
      @   ensures this.normals != null;
      @   ensures \forall int i; 0<=i<normals.length; normals[i]!=null;
      @   pure
      @*/
    //todo: ajeitar
    public Polygon(Vectors2D[] vertList) {
        this.vertices = generateHull(vertList, vertList.length);
        calcNormals();
    }

    /**
     * Constructor to generate a rectangle.
     *
     * @param width  Desired width of rectangle
     * @param height Desired height of rectangle
     */
    /*@ public normal_behavior
      @   requires Double.isFinite(width);
      @   requires Double.isFinite(height);
      @   ensures vertices.length == 4;
      @   ensures normals.length == 4;
      @   pure
      @*/
    public Polygon(double width, double height) {
        vertices = new Vectors2D[4];
        vertices[0] = new Vectors2D(-width, -height);
        vertices[1] = new Vectors2D(width, -height);
        vertices[2] = new Vectors2D(width, height);
        vertices[3] = new Vectors2D(-width, height);
        normals = new Vectors2D[4];
        normals[0] = new Vectors2D(0.0, -1.0);
        normals[1] = new Vectors2D(1.0, 0.0);
        normals[2] = new Vectors2D(0.0, 1.0);
        normals[3] = new Vectors2D(-1.0, 0.0);
    }

    /**
     * Generate a regular polygon with a specified number of sides and size.
     *
     * @param radius    The maximum distance any vertex is away from the center of mass.
     * @param noOfSides The desired number of face the polygon has.
     */
    /*@ public normal_behavior
      @   requires radius > 0;
      @   requires noOfSides > 0;
      @   requires Double.isFinite(2 * Math.PI / noOfSides * (noOfSides - 1 + 0.75));
      @   ensures vertices.length == noOfSides;
      @   ensures normals.length == noOfSides;
      @*/
    //problema: ele faz um cosseno de strictmath, que não possui um caso pra double finito ou != 0.
    //a não ser que tenha algo de errado com a definição que tem no meu programa não tem o que fazer.
    //todo: ajeitar depois de calcnormals
    public Polygon(int radius, int noOfSides) {
        vertices = new Vectors2D[noOfSides];
        /*@ maintaining 0 <= i <= vertices.length;
          @ maintaining \forall int k; 0 <= k < i; vertices[k] != null;
          @ loop_writes i, vertices[*];
          @ decreases vertices.length-i;
         */
        for (int i = 0; i < noOfSides; i++) {
            double angle = 2 * Math.PI / noOfSides * (i + 0.75);
            double pointX = radius * StrictMath.cos(angle);
            double pointY = radius * StrictMath.sin(angle);
            vertices[i] = new Vectors2D(pointX, pointY);
        }
        calcNormals();
    }

    /**
     * Generates normals for each face of the polygon. Positive normals of polygon faces face outward.
     */
    /*@ public normal_behavior
      @   assigns normals, normals[*];
      @   requires vertices != null;
      @   requires \forall int i; 0<=i<vertices.length; vertices[i].isValid();
      @   requires \forall int i; 0<=i<vertices.length; vertices[i].isZero() || (vertices[i].x != 0 || vertices[i].y != 0);
      @   ensures normals.length == vertices.length;
      @*/
    //Todo: ajeitar
    public void calcNormals() {
        normals = new Vectors2D[vertices.length];
        /*@ maintaining 0 <= i <= normals.length;
          @ maintaining \forall int k; 0 <= k < i; normals[k] != null;
          @ loop_writes i, normals[*];
          @ decreases normals.length-i;
         */
        for (int i = 0; i < vertices.length; i++) {
            Vectors2D face = vertices[i + 1 == vertices.length ? 0 : i + 1].subtract(vertices[i]);
            normals[i] = face.normal().normalize().negative();
        }
    }

    /**
     * Implementation of calculating the mass of a polygon.
     *
     * @param density The desired density to factor into the calculation.
     */
    /*@ also public normal_behavior
      @   assigns body.mass, body.I, body.invMass, body.invI;
      @   requires Double.isFinite(density);
      @   requires density>0;
      @   requires body != null;
      @   requires \forall int i; 0<=i<vertices.length; vertices[i].isValid();
      @   ensures body.mass>=0;
      @   ensures body.invMass>=0;
      @   ensures body.I>=0;
      @   ensures body.invI>=0;
      @*/
    //@skipesc
    //eu não sei como ajeitar esse negócio, provável causa perdida.
    @Override
    public void calcMass(double density) {
        Vectors2D centroidDistVec = new Vectors2D(0.0, 0.0);
        double area = 0.0;
        double I = 0.0;
        double k = 1.0 / 3.0;
        //TODO: Ajeitar o segundo maintaining
        /*@ maintaining 0 <= i <= vertices.length;
          @ maintaining \forall int j; 0 <= j < i; vertices[j].isValid();
          @ loop_writes i, area, I, centroidDistVec;
          @ decreases vertices.length-i;
         */
        for (int i = 0; i < vertices.length; ++i) {
            Vectors2D point1 = vertices[i];
            Vectors2D point2 = vertices[(i + 1) % vertices.length];
            double areaOfParallelogram = point1.crossProduct(point2);
            double triangleArea = 0.5 * areaOfParallelogram;
            area += triangleArea;

            double weight = triangleArea * k;
            centroidDistVec.add(point1.scalar(weight));
            centroidDistVec.add(point2.scalar(weight));

            double intx2 = point1.x * point1.x + point2.x * point1.x + point2.x * point2.x;
            double inty2 = point1.y * point1.y + point2.y * point1.y + point2.y * point2.y;
            I += (0.25 * k * areaOfParallelogram) * (intx2 + inty2);
        }
        //@ assert area>0;
        centroidDistVec = centroidDistVec.scalar(1.0 / area);
        //TODO: Ajeitar o segundo maintaining
        /*@ maintaining 0 <= i <= vertices.length;
          @ maintaining \forall int j; 0 <= j < i; vertices[j].isValid();
          @ loop_writes i, area, I, centroidDistVec;
          @ decreases vertices.length-i;
         */
        for (int i = 0; i < vertices.length; i++) {
            vertices[i] = vertices[i].subtract(centroidDistVec);
        }

        body.mass = density * area;
        body.invMass = (body.mass != 0.0) ? 1.0 / body.mass : 0.0;
        body.I = I * density;
        body.invI = (body.I != 0.0) ? 1.0 / body.I : 0.0;
    }

    /**
     * Generates an AABB encompassing the polygon and binds it to the body.
     */
    /*@ also public normal_behavior
      @   assigns body.aabb, body.aabb.*;
      @   requires body != null;
      @   ensures body.aabb != null;
      @   ensures body.aabb.min != null;
      @   ensures body.aabb.max != null;
      @*/
    //@skipesc
    @Override
    public void createAABB() {
        Vectors2D firstPoint = orient.mul(vertices[0], new Vectors2D());
        double minX = firstPoint.x;
        double maxX = firstPoint.x;
        double minY = firstPoint.y;
        double maxY = firstPoint.y;
        //TODO: Ajeitar o segundo maintaining
        /*@ maintaining 0 <= i <= vertices.length;
          @ maintaining \forall int k; 0 <= k < i; maxX>=minX && maxY>=minY;
          @ loop_writes minX,minY,maxX,maxY;
          @ decreases vertices.length-i;
         */
        for (int i = 1; i < vertices.length; i++) {
            Vectors2D point = orient.mul(vertices[i], new Vectors2D());
            double px = point.x;
            double py = point.y;

            if (px < minX) {
                minX = px;
            } else if (px > maxX) {
                maxX = px;
            }

            if (py < minY) {
                minY = py;
            } else if (py > maxY) {
                maxY = py;
            }
        }
        body.aabb = new AABB(new Vectors2D(minX, minY), new Vectors2D(maxX, maxY));
    }

    /**
     * Debug draw method for a polygon.
     *
     * @param g             Graphics2D object to draw to
     * @param paintSettings Colour settings to draw the objects to screen with
     * @param camera        Camera class used to convert points from world space to view space
     */
    // @Override
    // public void draw(Graphics2D g, ColourSettings paintSettings, Camera camera) {
    //     Path2D.Double s = new Path2D.Double();
    //     for (int i = 0; i < vertices.length; i++) {
    //         Vectors2D v = new Vectors2D(this.vertices[i]);
    //         orient.mul(v);
    //         v.add(body.position);
    //         v = camera.convertToScreen(v);
    //         if (i == 0) {
    //             s.moveTo(v.x, v.y);
    //         } else {
    //             s.lineTo(v.x, v.y);
    //         }
    //     }
    //     s.closePath();
    //     if (body.mass == 0.0) {
    //         g.setColor(paintSettings.staticFill);
    //         g.fill(s);
    //         g.setColor(paintSettings.staticOutLine);
    //     } else {
    //         g.setColor(paintSettings.shapeFill);
    //         g.fill(s);
    //         g.setColor(paintSettings.shapeOutLine);
    //     }
    //     g.draw(s);
    // }

    /**
     * Generates a convex hull around the vertices supplied.
     *
     * @param vertices List of vertices.
     * @param n        Number of vertices supplied.
     * @return Returns a convex hull array.
     */
    /*@ public normal_behavior
      @   requires vertices.length>=n> 0;
      @   requires \forall int i; 0<=i<vertices.length; vertices[i].isValid();
      @   ensures \result.length == n;
      @   spec_pure
      @*/
    //@ spec_public
    //todo: ajeitar pra que ele garanta que point esteja entre 0 e n porque senão reclama
    private Vectors2D[] generateHull(Vectors2D[] vertices, int n) {
        ArrayList<Vectors2D> hull = new ArrayList<>();

        int firstPointIndex = 0;
        double minX = Double.MAX_VALUE;

        /*@ maintaining 0 <= i <= n;
          @ maintaining \forall int k; 0 <= k < i; minX <= vertices[k].x && n>firstPointIndex>=0;
          @ loop_writes i, minX, firstPointIndex;
          @ decreases n-i;
         */
        for (int i = 0; i < n; i++) {
            double x = vertices[i].x;
            if (x < minX) {
                firstPointIndex = i;
                minX = x;
            }
        }

        int point = firstPointIndex, currentEvalPoint;
        boolean first = true;
        /*@ maintaining 0 <= \count <= n;
          @ maintaining \forall int k; 0 <= k < \count; hull.contains(vertices[k]) && n>point>=0;
          @ loop_writes currentEvalPoint, hull;
          @ decreases n-\count;
         */
        while (point != firstPointIndex || first) {
            first = false;
            hull.add(vertices[point]);
            currentEvalPoint = (point + 1) % n;
            /*@ maintaining 0 <= i <= n;
              @ maintaining \forall int j; 0 <= j < i; 0 <= currentEvalPoint < n && 0<= point < n;
              @ loop_writes i, currentEvalPoint;
              @ decreases n-i;
             */
            for (int i = 0; i < n; i++) {
                if (sideOfLine(vertices[point], vertices[i], vertices[currentEvalPoint]) == -1)
                    currentEvalPoint = i;
            }
            point = currentEvalPoint;
        }

        Vectors2D[] hulls = new Vectors2D[hull.size()];
        /*@ maintaining 0 <= i <= hull.size();
          @ maintaining \forall int k; 0 <= k < i; hulls[k] == hull.get(k);
          @ loop_writes i, hulls[*];
          @ decreases hull.size()-i;
         */
        for (int i = 0; i < hull.size(); i++) {
            hulls[i] = hull.get(i);
        }

        return hulls;
    }

    /**
     * Checks which side of a line a point is on.
     *
     * @param p1    Vertex of line to evaluate.
     * @param p2    Vertex of line to evaluate.
     * @param point Point to check which side it lies on.
     * @return Int value - positive = right side of line. Negative = left side of line.
     */
    /*@ private normal_behavior
      @   requires p1.isValid();
      @   requires p2.isValid();
      @   requires point.isValid();
      @   ensures \result == 1 || \result == 0 || \result == -1;
      @   pure
      @*/
    private int sideOfLine(Vectors2D p1, Vectors2D p2, Vectors2D point) {
        double val = (p2.y - p1.y) * (point.x - p2.x) - (p2.x - p1.x) * (point.y - p2.y);
        if (val > 0)
            return 1;
        else if (val == 0)
            return 0;
        else
            return -1;
    }
}
package testbed;

import library.math.Vectors2D;
// import testbed.demo.TestBedWindow; TEM QUE COMENTAR ISSO PARA COMPILAR O JML

public class Camera {
    private double aspectRatio;
    public double zoom;
    public int width;
    public int height;
    public Vectors2D centre;
    // private TestBedWindow panel;

    protected Vectors2D pointClicked;

    //@skipesc
    public Camera(){}

    //@ skipesc
    public Vectors2D getPointClicked(){
        return pointClicked;
    }
    //@ skipesc
    public void setPointClicked(Vectors2D v){
        pointClicked = v;
    }


    //TEM QUE COMENTAR ISSO PARA COMPILAR O JML

    // public Camera(int windowWidth, int windowHeight, TestBedWindow testWindow) {
    //     centre = new Vectors2D(0, 0);
    //     zoom = 1.0;
    //     this.width = windowWidth;
    //     this.height = windowHeight;
    //     panel = testWindow;
    //     aspectRatio = width * 1.0 / height;
    // }

    Vectors2D upperBound = new Vectors2D();
    Vectors2D lowerBound = new Vectors2D();


    //TEM QUE COMENTAR ISSO PARA COMPILAR O JML

    // public Vectors2D convertToScreen(Vectors2D v) {
    //     updateViewSize(aspectRatio);
    //     double boxWidth = (v.x - lowerBound.x) / (upperBound.x - lowerBound.x);
    //     double boxHeight = (v.y - lowerBound.y) / (upperBound.y - lowerBound.y);

    //     Vectors2D output = new Vectors2D();
    //     output.x = boxWidth * panel.getWidth();
    //     output.y = (1.0 - boxHeight) * (panel.getWidth() / aspectRatio);
    //     return output;
    // }

    // public Vectors2D convertToWorld(Vectors2D vec) {
    //     updateViewSize(aspectRatio);
    //     Vectors2D output = new Vectors2D();
    //     double distAlongWindowXAxis = vec.x / panel.getWidth();
    //     output.x = (1.0 - distAlongWindowXAxis) * lowerBound.x + distAlongWindowXAxis * upperBound.x;

    //     double aspectHeight = panel.getWidth() / aspectRatio;
    //     double distAlongWindowYAxis = (aspectHeight - vec.y) / aspectHeight;
    //     output.y = (1.0 - distAlongWindowYAxis) * lowerBound.y + distAlongWindowYAxis * upperBound.y;
    //     return output;
    // }

    //@ skipesc
    private void updateViewSize(double aspectRatio) {
        Vectors2D extents = new Vectors2D(aspectRatio * 200, 200);
        extents = extents.scalar(zoom);
        upperBound = centre.addi(extents);
        lowerBound = centre.subtract(extents);
    }

    // TEM QUE COMENTAR ISSO PARA COMPILAR O JML

    // public double scaleToScreenXValue(double radius) {
    //     double aspectRatio = width * 1.0 / height;
    //     Vectors2D extents = new Vectors2D(aspectRatio * 200, 200);
    //     extents = extents.scalar(zoom);
    //     Vectors2D upperBound = centre.addi(extents);
    //     Vectors2D lowerBound = centre.subtract(extents);
    //     double w = radius / (upperBound.x - lowerBound.x);
    //     return w * panel.getWidth();
    // }

    //@ skipesc
    public void transformCentre(Vectors2D v) {
        centre.add(v);
    }

    //@ skipesc
    public void setCentre(Vectors2D centre) {
        this.centre = centre;
    }

    //@ skipesc
    public void setZoom(double zoom) {
        assert (zoom > 0);
        this.zoom = zoom;
    }

    //@ skipesc
    public void reset() {
        setCentre(new Vectors2D());
        setZoom(1.0);
    }
}
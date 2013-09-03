public class Foo_1 {

    public boolean b;

    public void pre1() {
        int v1 = 22;
        int v2 = v1;
        int v3 = v2;
        int v4 = v3;
        int v5 = v4;
    }

    public void post1() {
        int v1 = 22;
        int v2 = v1;
        int v3 = v1;
        int v4 = v1;
        int v5 = v1;
    }

    public void pre2() {
        int v1 = b ? 22 : 33;
        int v2 = v1;
        int v3 = v2;
        int v4 = v3;
        int v5 = v4;
    }

    public void post2() {
        int v1 = b ? 22 : 33;
        int v2 = v1;
        int v3 = v2; // this assignment is equiv to `v3 = v1` but CopyPropagator doesn't handle that.
        int v4 = v3; // what makes CopyPropagator go overly conservative in this example
        int v5 = v4; // is the fact that v1 has two source instructions (one for each of the possible values).
    }

}

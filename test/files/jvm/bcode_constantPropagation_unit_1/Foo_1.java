public class Foo_1 {

    public void pre1() {
        int x = 2 + 2;
        int y = 3 * 4;
        System.out.println(20 / 2);
    }

    public void post1() {
        int x = 4;
        int y = 12;
        System.out.println(10);
    }

    public void pre2() {
        int x = 2;
        x = 4 / 2;
    }

    public void post2() {
        int x = 2;
    }

}

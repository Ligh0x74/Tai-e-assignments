class MyTest {

    public static void main(String[] args) {
        A a = new B();
        a.f = 1;
        B b = (B) a;
        int x = b.f;

        B.s = 2;
        x = A.s;

        if (b.equals(a)) {
            x = b.f;
        }
    }
}

class A {
    static int s;
    int f;
}

class B extends A {

}

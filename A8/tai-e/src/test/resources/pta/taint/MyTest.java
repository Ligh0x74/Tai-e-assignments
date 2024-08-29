class MyTest {

    public static void main(String[] args) {
        testArgToBase1();
    }

    private static void testBaseToResult1() {
        A a = A.source();
        int x = a.baseToResult();
        A.sink(x);
    }

    private static void testArgToBase1() {
        A a = new A();
        a.argToBase(A.source());
        int x = a.baseToResult();
        A.sink(x);
    }
}

class A {
    static A source() {
        return new A();
    }

    static void sink(int x) {
    }

    static void sink(A a) {
    }

    int baseToResult() {
        return 0;
    }

    void argToBase(A a) {
    }
}

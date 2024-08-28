class MyTest {

    public static void main(String[] args) {
        testStatic1();testStatic2();testStatic3();testStatic4();
        testInstance1();testInstance2();testInstance3();testInstance4();
        testArray1();testArray2();testArray3();testArray4();testArray5();testArray6();testArray7();testArray8();testArray9();
        testCast1();testInt1();
    }

    private static void testStatic1() {
        int x = 0;
        B.s = 1;
        x = B.s;
    }

    private static void testStatic2() {
        int x = 0;
        B.s = 1;
        x = B.s;
        B.s = 2;
    }

    private static void testStatic3() {
        int x = 0;
        A.s = 1;
        x = B.s;
    }

    private static void testStatic4() {
        int x = 0;
        A.s = 1;
        x = B.s;
        B.s = 2;
    }

    private static void testInstance1() {
        int x = 0;
        A a = new A();
        a.f = 1;
        x = a.f;
    }

    private static void testInstance2() {
        int x = 0;
        A a = new A();
        a.f = 1;
        x = a.f;
        a.f = 2;
    }

    private static void testInstance3() {
        int x = 0;
        A a = new A();
        a.f = 1;
        A aa = a;
        x = aa.f;
    }

    private static void testInstance4() {
        int x = 0;
        A a = new A();
        a.f = 1;
        A aa = a;
        x = aa.f;
        aa.f = 2;
    }

    private static void testArray1() {
        int x = 0;
        int[] arr = new int[1];
        arr[0] = 1;
        x = arr[0];
    }

    private static void testArray2() {
        int x = 0;
        int[] arr = new int[1];
        arr[0] = 1;
        x = arr[0];
        arr[0] = 2;
    }

    private static void testArray3() {
        int x = 0;
        int[] arr = new int[1];
        arr[0] = 1;
        int[] aux = arr;
        x = aux[0];
    }

    private static void testArray4() {
        int x = 0;
        int[] arr = new int[1];
        arr[0] = 1;
        int[] aux = arr;
        x = aux[0];
        aux[0] = 2;
    }

    private static void testArray5() {
        int x = 0;
        int[] arr = new int[2];
        arr[0] = 1;
        x = arr[1];
        arr[1] = 2;
    }

    private static void testArray6() {
        int x = 0;
        int[] arr = new int[2];
        arr[0] = 1;
        int[] aux = arr;
        x = aux[1];
        aux[1] = 2;
    }

    private static void testArray7() {
        int x = 0;
        int[] arr = new int[2];
        int i = 1 / 0;
        arr[i] = 1;
        x = arr[i];
    }

    private static void testArray8() {
        int x = 0;
        int[] arr = new int[2];
        arr[0] = 1;
        x = arr[0];
        int i = 1 / 0;
        arr[i] = 2;
    }

    private static void testArray9() {
        int x = 0;
        int[] arr = new int[2];
        arr[0] = 1;
        x = arr[0];
        int i;
        if (arr.length < 0) {
            i = 0;
        } else {
            i = 1;
        }
        arr[i] = 2;
    }

    private static void testCast1() {
        int x = 0;
        A a = new B();
        a.f = 1;
        B b = (B) a;
        if (b.equals(a)) {
            x = b.f;
        }
    }

    private static void testInt1() {
        double[] arr = new double[1];
        arr[0] = 3.14;
        double x = arr[0];
    }
}

class A {
    static int s;
    int f;
}

class B extends A {

}

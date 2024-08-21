class MyTest {
    int MAX = 0x3f;

    void foo(int k, int z, boolean b, String s) {
        k++;
        MyTest my = new MyTest();
        k = my.MAX;
        my.MAX = 7;
        double pi = 3.14;
        k = (int) pi;
        k = 1 + (int) pi;

        k /= 0;
        k = 7;
        k /= 0;
        z = z + z;
        z = z + k;
        z = k + 1;
        z = 1 + 1;

        if (b) {
            k = 1;
            z = 1;
        }
    }
}
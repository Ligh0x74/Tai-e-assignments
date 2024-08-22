import java.util.Random;

class MyTest {

    int foo(int x) {
        int y;
        y = x; // dead
        y = 0;

        if (y == 0) {
            y = 1;
        } else {
            y = 2; // dead
        }

        y = y + 1; // dead

        if (x == 0) {
            y = 3;
        } else {
            y = 4;
        }

        switch (y) {
            case 1:
                y = 5;
                break;
            case 2:
                y = 6;
                break;
            default:
                y = 7;
                break;
        }

        y = y + 1; // dead

        y = 8;
        switch (y) {
            case 1:
                y = 5; // dead
                break;
            case 8:
                y = 9; // dead
            case 9:
                y = 10;
                break;
            default:
                y = 11; // dead
                break;
        }

        return y;
    }
}

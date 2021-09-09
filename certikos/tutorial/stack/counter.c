#define MAX_COUNTER ((unsigned int) 10)

static unsigned int COUNTER = 0;

unsigned int get_counter() {
    return COUNTER;
}

unsigned int incr_counter() {
    COUNTER = COUNTER + 1;
    return COUNTER;
}

unsigned int decr_counter() {
    COUNTER = COUNTER - 1;
    return COUNTER;
}

#include <unistd.h>

int main(int argc, char **argv) {
    int x = fork();
    return x;
}

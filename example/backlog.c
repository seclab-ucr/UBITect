#include <stdio.h>

enum engine_status {
        ENGINE_IDLE,
        ENGINE_BUSY,
        ENGINE_W_DEQUEUE,
};
struct test_struct{
        int irq;
        enum engine_status eng_st;
};
struct aStruct{
        enum engine_status eng_st;
};
struct test_struct *init;
struct aStruct *cpg;
int test(int a){
        struct test_struct *backlog;
        cpg->eng_st = ENGINE_BUSY;

        if (a){
                backlog = init;
        }

        if(backlog){
                backlog->irq = 0;
                cpg->eng_st = ENGINE_IDLE;
        }
        return 0;
}

#include <stdint.h>
#include <stdio.h>

#define BITS 32

uint32_t r1r = 1614753124;
uint32_t r1a = 972926864;
uint32_t r2 = 1699251772;
uint32_t k = 3301815156;
uint32_t ID = 2476422849;

uint32_t hash(uint32_t in) {
    // TODO: Make this into an actual hash function
    // Must be guaranteed to return an output <= BITS, as it is fed into a rotation
    uint32_t rtn = in % BITS;
    return rtn;
}

/* Function to respond to a authentication query in accordance with the CH07 protocol
   Params:
   r1 - the value of r1 given in the query
   myID - whether it is the attacker or a legitimate tag responding; 0 for a legitimate tag, 1 for the attacker
   episode - how many communications have been exchanged prior to this one
   buffer - pointer to the message buffer containing all sent/received messages
   Returns:
   void - places correct messages in the buffer in accordance with the protocol/attack
*/
void respond(uint32_t r1, int myID, int episode, uint32_t* buffer) {
    if (myID == 0) {
        // We are the legitimate tag
        uint32_t g = hash(r1 ^ r2 ^ k);
        // Hash function needs to guarantee g <= BITS
        // This implements bit rotation right (not specified in the protocol whether it should be right or left)
        uint32_t ID2 = ID >> g | ID << g;
        buffer[episode*3] = r2;
        buffer[episode*3 + 1] = (ID2^g) >> (BITS / 2);
    } else {
        // We are the attacker

        // Select some 3-argument operation based on information available to us
        /*
        Information available is:
            - r1a (since we created it)
            - Anything that has been sent over the wires
            - The r1 that is provided as input to this function
        NB: k and ID must *not* be available, as these are secret

        Operations available:
            - Bitwise ops AND, OR, XOR
            - Mathematical ops +,-,*,/ (with the result of the last two truncated)
                - Incl also v2-v1 and v2/v1, because these operations are not commutative
        */
        int AI_op1;
        int AI_op2;
        int AI_v1;
        int AI_v2;
        int AI_v3;
        uint32_t v_choices[2 + episode*3];
        v_choices[0] = r1a;
        v_choices[1] = r1;
        for (int i = 0; i < episode; i++) {
            v_choices[i+2] = buffer[i];
        }
        if (AI_v1 >= 2+episode*3 || AI_v2 >= episode*3 || AI_v3 >= episode*3) {
            // Return a nonsense value that won't be authenticated
            //buffer[episode*3] = 0;
            return;
        } else {
            uint32_t o_1;
            uint32_t r2_prime;
            if (AI_op1 == 0) {
                // Bitwise AND
                o_1 = v_choices[AI_v1] & v_choices[AI_v2];
            } else if (AI_op1 == 1) {
                // Bitwise OR
                o_1 = v_choices[AI_v1] | v_choices[AI_v2];
            } else if (AI_op1 == 2) {
                // Bitwise XOR
                o_1 = v_choices[AI_v1] ^ v_choices[AI_v2];
            } else if (AI_op1 == 3) {
                // Addition
                o_1 = v_choices[AI_v1] + v_choices[AI_v2];
            } else if (AI_op1 == 4) {
                // Subtraction
                o_1 = v_choices[AI_v1] - v_choices[AI_v2];
            } else if (AI_op1 == 5) {
                // Multiplication
                o_1 = v_choices[AI_v1] * v_choices[AI_v2];
            } else if (AI_op1 == 6) {
                // Division
                o_1 = v_choices[AI_v1] / v_choices[AI_v2];
            } else if (AI_op1 == 7) {
                // Subtraction - v2-v1
                o_1 = v_choices[AI_v2] - v_choices[AI_v1];
            } else if (AI_op1 == 8) {
                // Division - v2/v1
                o_1 = v_choices[AI_v2] / v_choices[AI_v1];
            }

            // Second operation - applied to v3 and the outcome of operation 1 (o_1)
            if (AI_op2 == 0) {
                // Bitwise AND
                r2_prime = o_1 & v_choices[AI_v3];
            } else if (AI_op2 == 1) {
                // Bitwise OR
                r2_prime = o_1 | v_choices[AI_v3];
            } else if (AI_op2 == 2) {
                // Bitwise XOR
                r2_prime = o_1 ^ v_choices[AI_v3];
            } else if (AI_op2 == 3) {
                // Addition
                r2_prime = o_1 + v_choices[AI_v3];
            } else if (AI_op2 == 4) {
                // Subtraction
                r2_prime = o_1 - v_choices[AI_v3];
            } else if (AI_op2 == 5) {
                // Multiplication
                r2_prime = o_1 * v_choices[AI_v3];
            } else if (AI_op2 == 6) {
                // Division
                r2_prime = o_1 / v_choices[AI_v3];
            } else if (AI_op2 == 7) {
                // Subtraction - v3-o_1
                r2_prime = v_choices[AI_v3] - o_1;
            } else if (AI_op2 == 8) {
                // Division - v3/o_1
                r2_prime = v_choices[AI_v3] / o_1;
            }
            buffer[episode*3] = r2_prime;
            // Second part to send - just send some piece of information we've seen/created, as above
            // Note that this includes the bits needed for the attack, as that is seen over the wires
            int AI_m2_choice;
            if (AI_m2_choice >= 2+episode*3) {
                return;
                //buffer[episode*3 + 1] = 0;
            } else {
                buffer[episode*3 + 1] = v_choices[AI_m2_choice];
            }
        }
    }
}


int main() {
    int auth_violated = 0;

    uint32_t msg_buffer[6];
    // IDs of senders and receivers - 1 is always the attacker, 0 is the legitimate sender/receiver
    int AI_first_tag;// = 0;
    int AI_second_tag;// = 1;

    int AI_first_recv;// = 1;
    int AI_second_recv;// = 0;

    // Main essentially is the receiver - function calls to respond encode tag behaviour

    // Boundary check our variables for senders/receivers
    __CPROVER_assume(AI_first_recv==0 || AI_first_recv == 1);
    __CPROVER_assume(AI_second_recv==0 || AI_second_recv == 1);
    __CPROVER_assume(AI_first_tag == 0 || AI_first_tag == 1);
    __CPROVER_assume(AI_second_tag == 0 || AI_second_tag == 1);

    // First communication
    if (AI_first_recv == 0) {
        // We are the legitimate receiver
        printf("Buffer vals before respond call %d, %d\n", msg_buffer[0], msg_buffer[1]);
        respond(r1r, AI_first_tag, 0, msg_buffer);
        printf("Buffer vals after respond call %d, %d\n", msg_buffer[0], msg_buffer[1]);
        // Decide whether we can use r1r to recover that left half of ID2
        uint32_t r2_recovered = msg_buffer[0];
        uint32_t match_bits = msg_buffer[1];
        uint32_t g_local = hash(r1r^r2_recovered^k);
        uint32_t ID2_local = ID >> g_local | ID << g_local;
        uint32_t match_local = (ID2_local^g_local) >> (BITS/2);
        if (match_local == match_bits) {
            // Authenticate, send the right half over the wire
            msg_buffer[2] = ((ID2_local^g_local) << (BITS/2)) >> (BITS/2);
            printf("Authenticated!\n");
            if (AI_first_tag == 1) {
                // We've just authenticated the attacker, so the security condition has been breached
                //auth_violated = 1;
            }
        }
    } else {
        // We are the attacker
        // Check we're not sending a message to ourselves, as that doesn't make sense
        if (AI_first_tag == 1) {
            goto exit;
        }
        respond(r1a, AI_first_tag, 0, msg_buffer);
        // No need to manipulate these values further
    }

    // Second communication
    if (AI_second_recv == 0) {
        // We are the legitimate receiver
        printf("Buffer vals before respond call %d, %d\n", msg_buffer[3], msg_buffer[4]);
        respond(r1r, AI_second_tag, 1, msg_buffer);
        printf("Buffer vals after respond call %d, %d\n", msg_buffer[3], msg_buffer[4]);
        // Decide whether we can use r1r to recover that left half of ID2
        uint32_t r2_recovered = msg_buffer[3];
        uint32_t match_bits = msg_buffer[4];
        uint32_t g_local = hash(r1r^r2_recovered^k);
        uint32_t ID2_local = ID >> g_local | ID << g_local;
        uint32_t match_local = (ID2_local^g_local) >> (BITS/2);
        if (match_local == match_bits) {
            // Authenticate, send the right half over the wire
            msg_buffer[5] = ((ID2_local^g_local) << (BITS/2)) >> (BITS/2);
            printf("Authenticated!\n");
            if (AI_second_tag == 1) {
                // We've just authenticated the attacker, so the security condition has been breached
                auth_violated = 1;
                printf("Authenticated attacker!\n");
            }
        }
    } else {
        // We are the attacker
        // Check we're not sending a message to ourselves, as that doesn't make sense
        if (AI_second_tag == 1) {
            goto exit;
        }
        respond(r1a, AI_second_tag, 1, msg_buffer);
        // No need to manipulate these values further
    }


    // Check if the security condition was violated at any point
    exit:
    __CPROVER_assert(auth_violated != 1, "Authenticated the attacker");
}
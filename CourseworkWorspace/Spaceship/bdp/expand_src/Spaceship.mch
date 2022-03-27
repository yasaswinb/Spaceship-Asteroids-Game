/* Spaceship
 * Author: Yasaswin
 * Creation date: 2021-11-20
 */
MACHINE
    Spaceship

SETS
    SPACESHIP_STATUS = { docked_at_Starbase , current_location_is_the_Homebase , currently_not_docked } ;

    STATES_OF_GAME = { Game_Not_Started_Yet , Won_The_Game , Lost_The_Game , Game_Not_Over } ;

    REPORT = { Moved_Successfully , Movement_Failed_Due_To_Unknown_Space_Boundary , Failed_Due_To_Insufficient_Power ,
               Asteroid_Collided_Movement_Failed , Failed_Due_Insufficient_Power_To_Happen_A_Collision , Warp_Drive_Successful ,
               Warp_Drive_Failed_Due_To_Same_Position ,
               Warp_Drive_Failed_Due_To_Unknown_Space_Boundary , Warp_Drive_Failed_Due_To_Insufficient_Power ,
               Warp_Drive_Failed_Due_To_Asteroid_Collision }


CONCRETE_CONSTANTS
    grid_x_width , // width range of the grid
    grid_y_height , // height range of the grid
    warp_grid_x_width , //for the ease of demonstration of available operations the preference for the warp drive coordinates x range has being limited to 15 but they could be infinite
    warp_grid_y_height , //for the ease of demonstration of available operations the preference for the warp drive coordinates y range has being limited to 15 but they could be infinite
    grid_x_limit , //maximum width of the grid
    grid_y_limit , //maximum height of the grid
    GRID ,        //Cartesian product of the GRID (SPACE)
    Homebase ,    //home base location 
    Starbase ,    //star base base location 
    ASTEROIDS ,   //locations of asteroids
    Normal_Move_Power , //power which will be consumed for a normal move
        Warp_Drive_Power , //power which will be consumed for a warp drive
        Spaceship_Crash_Power_Loss //the power which will be lost in a collision

PROPERTIES
    grid_x_width <: NAT1 & grid_x_width = 1 .. 12 &
    grid_y_height <: NAT1 & grid_y_height = 1 .. 7 &

    warp_grid_x_width <: NAT1 & warp_grid_x_width = 1 .. 15 & //for the ease of demonstration of available operations the preference for the warp drive coordinates x range has being limited to 15 but they could be infinite
    warp_grid_y_height <: NAT1 & warp_grid_y_height = 1 .. 15 & //for the ease of demonstration of available operations the preference for the warp drive coordinates y range has being limited to 15 but they could be infinite

    grid_x_limit : grid_x_width & grid_x_limit = 12 &
    grid_y_limit : grid_y_height & grid_y_limit = 7 &

    GRID : grid_x_width <-> grid_y_height & GRID = grid_x_width * grid_y_height &
    Homebase : GRID & Homebase = ( 1 |-> 1 ) &
    Starbase : GRID & Starbase = ( 6 |-> 4 ) &
    ASTEROIDS <: GRID & ASTEROIDS = { ( 3 |-> 2 ) , ( 3 |-> 5 ) , ( 5 |-> 4 ) , ( 6 |-> 7 ) , ( 7 |-> 1 ) , ( 7 |-> 5 ) , ( 7 |-> 7 ) , ( 8 |-> 3 ) , ( 10 |-> 6 ) ,
               ( 11 |-> 2 ) , ( 12 |-> 5 ) } &

    Normal_Move_Power : NAT1 & Normal_Move_Power = 5 &
        Warp_Drive_Power : NAT1 & Warp_Drive_Power = 20 &
        Spaceship_Crash_Power_Loss : NAT1 & Spaceship_Crash_Power_Loss = 10

DEFINITIONS
    isWithinTheSpaceGrid ( x_position , y_position ) == ( ( x_position |-> y_position ) : GRID ) ;
    isAsteroid ( x_position , y_position ) == ( ( x_position |-> y_position ) : ASTEROIDS ) ;
    isStarbase ( x_position , y_position ) == ( ( x_position |-> y_position ) = Starbase ) ;
    isHomebase ( x_position , y_position ) == ( ( x_position |-> y_position ) = Homebase ) ;

    ANIMATION_FUNCTION == ( { row , col , img | row : grid_y_height & col : grid_x_width &
                        ( IF ( isStarbase ( current_x_position , ( 8 - current_y_position ) ) or ( current_spaceship_power < Normal_Move_Power & size ( visited_regions ) > 0 ) )
                            THEN
                                //Game lost state
                                img = 1
                            ELSE
                                IF ( isStarbase ( col , ( 8 - row ) ) )
                                   THEN
                                       //Starbase
                                       img = 4
                                   ELSE
                                       IF ( isAsteroid ( col , ( 8 - row ) ) )
                                       THEN
                                           //Asteroid
                                           img = 2
                                       ELSE
                                           IF ( row = ( 8 - current_y_position ) & col = ( current_x_position ) )
                                               THEN
                                                   //Spaceship
                                                   img = 3
                                               ELSE
                                                   img = 1
                                           END
                                       END
                                 END
                           END ) } ) ;

                ANIMATION_IMG1 == "Images/empty.gif" ;
                ANIMATION_IMG2 == "Images/asteroid.gif" ;
                ANIMATION_IMG3 == "Images/spaceship.gif" ;
                ANIMATION_IMG4 == "Images/starbase.gif" ;

ABSTRACT_VARIABLES
    asteroid_collision_count , //collision count of the asteroids
    current_spaceship_power , //current power of the spaceship
    visited_regions , //sequence of the visited regions
    current_x_position , //spaceship x axis position
    current_y_position //spaceship y axis position

INVARIANT
    asteroid_collision_count : NAT &
    current_spaceship_power : NAT &
    visited_regions : seq ( GRID ) &
    current_x_position : NAT1 & current_x_position : grid_x_width &
    current_y_position : NAT1 & current_y_position : grid_y_height


INITIALISATION
    asteroid_collision_count , current_spaceship_power , visited_regions , current_x_position , current_y_position := 0 , 0 , [] , 1 , 1

OPERATIONS

    /**
    inquiry operations 
    **/

    ship_location , spaceship_power , collision_count <-- MissionStatus =
    BEGIN
        ship_location := ( current_x_position |-> current_y_position )
        ||
        spaceship_power := current_spaceship_power
        ||
        collision_count := asteroid_collision_count
    END ;


    regions_visited <-- RegionsVisited =
    BEGIN
        regions_visited := visited_regions
    END ;


    status_of_spaceship <-- DockedAtStarbase =
    PRE status_of_spaceship : SPACESHIP_STATUS
    THEN
        IF ( isStarbase ( current_x_position , current_y_position ) ) //this will check whether if the current coordinate is the location of the Starbase
        THEN
            status_of_spaceship := docked_at_Starbase
        ELSIF ( isHomebase ( current_x_position , current_y_position ) ) //this will check whether if the current coordinate is the location of the Homebase
        THEN
            status_of_spaceship := current_location_is_the_Homebase
        ELSE //if the current position is not Starbase or Homebase the ship is not docked
           status_of_spaceship := currently_not_docked
        END
    END ;


    status_of_the_game <-- GameStatus =
    PRE status_of_the_game : STATES_OF_GAME
    THEN
        IF ( isStarbase ( current_x_position , current_y_position ) ) //this will check whether if the current coordinate is the location of the Starbase
        THEN
            status_of_the_game := Won_The_Game
        ELSIF ( not ( isStarbase ( current_x_position , current_y_position ) ) &
                current_spaceship_power >= Normal_Move_Power &
                isWithinTheSpaceGrid ( current_x_position , current_y_position ) ) //this will check whether if the current coordinate is not the location of the Starbase and current while current spaceship power is greater than or equal to 5 and within the grid
        THEN
            status_of_the_game := Game_Not_Over
        ELSIF ( size ( visited_regions ) = 0 ) //this will check whether the visited_regions size is 0
        THEN
            status_of_the_game := Game_Not_Started_Yet
        ELSIF ( current_spaceship_power < Normal_Move_Power ) //this will check whether the spaceship power is less than 5
        THEN
            status_of_the_game := Lost_The_Game
        END
    END ;


    NewGame ( power ) =
    PRE power : NAT & power <= 100 & power >= 5 //minimum power is allocated to 5 hence the minimum power required operation uses 5 points to perform a move
    THEN
        current_spaceship_power := power
        ||
        asteroid_collision_count := 0
        ||
        visited_regions := [ 1 |-> 1 ]
        ||
        current_x_position := 1
        ||
        current_y_position := 1
    END ;

    /**
    Normal moves 
    **/

    report <-- MoveUp =
    PRE report : REPORT & ( not ( isStarbase ( current_x_position , current_y_position ) ) ) & ( current_spaceship_power >= Normal_Move_Power ) // to make available this operation report need to be an element of REPORT set while current position is not equal to Starbase and current spaceship power is greater than or equal to 5
    THEN
        IF ( current_spaceship_power < Normal_Move_Power ) //if the power is lower than the 5 this will be executed
        THEN
            report := Failed_Due_To_Insufficient_Power

        ELSIF ( not ( isWithinTheSpaceGrid ( current_x_position , succ ( current_y_position ) ) ) ) //if the current position is not an element of grid this will be executed
        THEN
            report := Movement_Failed_Due_To_Unknown_Space_Boundary

        ELSIF ( isAsteroid ( current_x_position , succ ( current_y_position ) ) & current_spaceship_power >= Spaceship_Crash_Power_Loss ) //if the spaceship collide with an asteroid and the current power is greater than or equal to 10 this will be executed
        THEN
            report := Asteroid_Collided_Movement_Failed
            ||
            asteroid_collision_count := succ ( asteroid_collision_count )
            ||
            current_spaceship_power := current_spaceship_power - Spaceship_Crash_Power_Loss

        ELSIF ( isAsteroid ( current_x_position , succ ( current_y_position ) ) & current_spaceship_power < Spaceship_Crash_Power_Loss ) //if the spaceship collide with an asteroid but the current power is less than 10 this will be executed
        THEN
            report :=  Failed_Due_Insufficient_Power_To_Happen_A_Collision
        ELSE //if above all scenarios are false this success scenario will be executed  
            report := Moved_Successfully
            ||
            current_x_position , current_y_position := current_x_position , succ ( current_y_position )
            ||
            visited_regions := visited_regions <- ( current_x_position |-> succ ( current_y_position ) )
            ||
            current_spaceship_power := current_spaceship_power - Normal_Move_Power
        END
    END ;


    report <-- MoveDown =
    PRE report : REPORT & ( not ( isStarbase ( current_x_position , current_y_position ) ) ) & ( current_spaceship_power >= Normal_Move_Power )
    THEN
        IF ( current_spaceship_power < Normal_Move_Power )
        THEN
            report := Failed_Due_To_Insufficient_Power

        ELSIF ( not ( isWithinTheSpaceGrid ( current_x_position , pred ( current_y_position ) ) ) )
        THEN
            report := Movement_Failed_Due_To_Unknown_Space_Boundary

        ELSIF ( isAsteroid ( current_x_position , pred ( current_y_position ) ) & current_spaceship_power >= Spaceship_Crash_Power_Loss )
        THEN
            report := Asteroid_Collided_Movement_Failed
            ||
            asteroid_collision_count := succ ( asteroid_collision_count )
            ||
            current_spaceship_power := current_spaceship_power - Spaceship_Crash_Power_Loss

        ELSIF ( isAsteroid ( current_x_position , pred ( current_y_position ) ) & current_spaceship_power < Spaceship_Crash_Power_Loss )
        THEN
            report :=  Failed_Due_Insufficient_Power_To_Happen_A_Collision

        ELSE
            report := Moved_Successfully
            ||
            current_x_position , current_y_position := current_x_position , pred ( current_y_position )
            ||
            visited_regions := visited_regions <- ( current_x_position |-> pred ( current_y_position ) )
            ||
            current_spaceship_power := current_spaceship_power - Normal_Move_Power
        END
    END ;


    report <-- MoveForward =
    PRE report : REPORT & ( not ( isStarbase ( current_x_position , current_y_position ) ) ) & ( current_spaceship_power >= Normal_Move_Power )
    THEN
        IF ( current_spaceship_power < Normal_Move_Power )
        THEN
            report := Failed_Due_To_Insufficient_Power

        ELSIF ( not ( isWithinTheSpaceGrid ( succ ( current_x_position ) , current_y_position ) ) )
        THEN
            report := Movement_Failed_Due_To_Unknown_Space_Boundary

        ELSIF ( isAsteroid ( succ ( current_x_position ) , current_y_position ) & current_spaceship_power >= Spaceship_Crash_Power_Loss )
        THEN
            report := Asteroid_Collided_Movement_Failed
            ||
            asteroid_collision_count := succ ( asteroid_collision_count )
            ||
            current_spaceship_power := current_spaceship_power - Spaceship_Crash_Power_Loss

        ELSIF ( isAsteroid ( succ ( current_x_position ) , ( current_y_position ) ) & current_spaceship_power < Spaceship_Crash_Power_Loss )
        THEN
            report :=  Failed_Due_Insufficient_Power_To_Happen_A_Collision

        ELSE
            report := Moved_Successfully
            ||
            current_x_position , current_y_position := succ ( current_x_position ) , current_y_position
            ||
            visited_regions := visited_regions <- ( succ ( current_x_position ) |-> current_y_position )
            ||
            current_spaceship_power := current_spaceship_power - Normal_Move_Power
        END
    END ;


    report <-- MoveBackward =
    PRE report : REPORT & ( not ( isStarbase ( current_x_position , current_y_position ) ) ) & ( current_spaceship_power >= Normal_Move_Power )
    THEN
        IF ( current_spaceship_power < Normal_Move_Power )
        THEN
            report := Failed_Due_To_Insufficient_Power

        ELSIF ( not ( isWithinTheSpaceGrid ( pred ( current_x_position ) , current_y_position ) ) )
        THEN
            report := Movement_Failed_Due_To_Unknown_Space_Boundary

        ELSIF ( isAsteroid ( pred ( current_x_position ) , current_y_position ) & current_spaceship_power >= Spaceship_Crash_Power_Loss )
        THEN
            report := Asteroid_Collided_Movement_Failed
            ||
            asteroid_collision_count := succ ( asteroid_collision_count )
            ||
            current_spaceship_power := current_spaceship_power - Spaceship_Crash_Power_Loss

        ELSIF ( isAsteroid ( pred ( current_x_position ) , ( current_y_position ) ) & current_spaceship_power < Spaceship_Crash_Power_Loss )
        THEN
            report :=  Failed_Due_Insufficient_Power_To_Happen_A_Collision

        ELSE
            report := Moved_Successfully
            ||
            current_x_position , current_y_position := pred ( current_x_position ) , current_y_position
            ||
            visited_regions := visited_regions <- ( pred ( current_x_position ) |-> current_y_position )
            ||
            current_spaceship_power := current_spaceship_power - Normal_Move_Power
        END

    END ;

    /**
    warp drive operations 
    **/

    report <-- EngageWarpDrive ( position ) =
    PRE position : warp_grid_x_width * warp_grid_y_height &
        ( current_spaceship_power >= Normal_Move_Power ) & not ( isStarbase ( current_x_position , current_y_position ) ) //this operation will available if the position parameter is within the range of above specified 15 by 15 grid (which could be infinite but for the ease of representing all the operations limited to 15) while current spaceship power is greater than or equal to 5 and current position is not equal to Starbase
    THEN
        IF ( current_spaceship_power < Warp_Drive_Power ) //if the current spaceship power is less than 20 this will be executed
        THEN
            report := Warp_Drive_Failed_Due_To_Insufficient_Power

        ELSIF ( not ( isWithinTheSpaceGrid ( prj1 ( warp_grid_x_width , warp_grid_y_height ) ( position ) , prj2 ( warp_grid_x_width , warp_grid_y_height ) ( position ) ) ) ) //if the parameter position not an element of grid this will be executed 
        THEN
            report := Warp_Drive_Failed_Due_To_Unknown_Space_Boundary

        ELSIF ( prj1 ( warp_grid_x_width , grid_y_height ) ( position ) = current_x_position & prj2 ( warp_grid_x_width , grid_y_height ) ( position ) = current_y_position ) //if the warp drive executed to the same position where the spaceship landed this will be executed
        THEN
            report := Warp_Drive_Failed_Due_To_Same_Position

        ELSIF ( isAsteroid ( prj1 ( warp_grid_x_width , grid_y_height ) ( position ) , prj2 ( warp_grid_x_width , grid_y_height ) ( position ) ) ) //if the spaceship collide with an asteroid this will be executed
        THEN
            report := Warp_Drive_Failed_Due_To_Asteroid_Collision
            ||
            asteroid_collision_count := succ ( asteroid_collision_count )
            ||
            current_spaceship_power := current_spaceship_power - Spaceship_Crash_Power_Loss

        ELSE //if all the above scenarios are false the success scenario will be executed
            report := Warp_Drive_Successful
            ||
            current_x_position , current_y_position := prj1 ( warp_grid_x_width , grid_y_height ) ( position ) , prj2 ( warp_grid_x_width , grid_y_height ) ( position )
            ||
            visited_regions := visited_regions <- ( prj1 ( warp_grid_x_width , grid_y_height ) ( position ) |-> prj2 ( warp_grid_x_width , grid_y_height ) ( position ) )
            ||
            current_spaceship_power := current_spaceship_power - Warp_Drive_Power
        END
    END

END

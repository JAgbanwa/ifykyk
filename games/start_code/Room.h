//
// Created by Tim Apers on 29/10/2024.
//

#ifndef ROOM_H
#define ROOM_H

#include "Entity.h"

class Room {
public:
    // Deze functie niet aanpassen!
    void render(sf::RenderWindow* window) const;

    // Deze functie zal je zelf verder moeten aanvullen
    void update(sf::Event* event);

private:
    std::vector<Entity*> entities;
};



#endif //ROOM_H

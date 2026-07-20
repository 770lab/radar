/* ============ RADAR — géoloc partagée en direct ============
 * Chaque visiteur qui accepte la géoloc apparaît sur la carte
 * de tous les autres, tant que sa page reste ouverte.
 * Présence : RTDB /presence/$uid + onDisconnect().remove()
 */
(function () {
  'use strict';

  // ---------- Constantes ----------
  var STALE_MS = 75 * 1000;        // au-delà : blip grisé
  var ZOMBIE_MS = 10 * 60 * 1000;  // au-delà : nettoyage du nœud (autorisé par les règles)
  var HEARTBEAT_MS = 25 * 1000;    // refresh du timestamp sans mouvement
  var WRITE_MIN_MS = 2500;         // délai mini entre deux écritures de position
  var WRITE_MIN_METERS = 3;        // ou déplacement mini
  var SHARE_URL = 'https://770lab.com/radar/';

  var CALLSIGNS = [
    'Renard', 'Faucon', 'Lynx', 'Panthère', 'Aigle', 'Loup', 'Colibri',
    'Orque', 'Tigre', 'Cobra', 'Puma', 'Corbeau', 'Gazelle', 'Bison',
    'Phénix', 'Mangouste', 'Vipère', 'Condor', 'Jaguar', 'Belette'
  ];

  // ---------- DOM ----------
  var $ = function (id) { return document.getElementById(id); };
  var elGate = $('gate'), elGateCount = $('gate-count'), elGateError = $('gate-error');
  var elCallsign = $('callsign'), elJoin = $('btn-join'), elReroll = $('btn-reroll');
  var elHud = $('hud'), elHudCount = $('hud-count'), elRoster = $('roster'), elToasts = $('toasts');

  // ---------- État ----------
  var map, tiles;
  var db, meRef, myUid = null;
  var joined = false;
  var joining = false;
  var gotFirstSnapshot = false;
  var follow = true;
  var suppressMoveEvents = false; // pans programmatiques ≠ drag utilisateur
  var watchId = null, heartbeatTimer = null, repaintTimer = null;
  var serverOffset = 0;
  var lastFix = null;            // dernier GeolocationPosition reçu
  var lastPayload = null;        // dernier objet écrit dans la DB
  var lastWriteAt = 0;
  var people = {};               // uid -> data
  var markers = {};              // uid -> { marker, sig }
  var accCircle = null;
  var knownUids = null;          // pour les toasts arrivée/départ
  var cleanedUids = {};          // zombies déjà nettoyés cette session
  var rosterSig = '';            // évite de reconstruire le roster à l'identique
  var repaintQueued = false;
  var lastRepaintAt = 0;

  // ---------- Utilitaires ----------
  function escapeHtml(s) {
    return String(s).replace(/[&<>"']/g, function (c) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c];
    });
  }

  function randomCallsign() {
    var animal = CALLSIGNS[Math.floor(Math.random() * CALLSIGNS.length)];
    var num = String(Math.floor(Math.random() * 90) + 10);
    return animal + '-' + num;
  }

  function cleanName(raw) {
    return String(raw || '').replace(/\s+/g, ' ').trim().slice(0, 20);
  }

  function hueFromUid(uid) {
    var h = 0;
    for (var i = 0; i < uid.length; i++) h = (h * 31 + uid.charCodeAt(i)) >>> 0;
    return h % 360;
  }

  function colorFor(hue) { return 'hsl(' + hue + ', 90%, 62%)'; }

  function serverNow() { return Date.now() + serverOffset; }

  function haversine(lat1, lng1, lat2, lng2) {
    var R = 6371000, rad = Math.PI / 180;
    var dLat = (lat2 - lat1) * rad, dLng = (lng2 - lng1) * rad;
    var a = Math.sin(dLat / 2) * Math.sin(dLat / 2) +
      Math.cos(lat1 * rad) * Math.cos(lat2 * rad) *
      Math.sin(dLng / 2) * Math.sin(dLng / 2);
    return 2 * R * Math.asin(Math.sqrt(a));
  }

  function formatDist(m) {
    if (!isFinite(m)) return '';
    if (m < 1000) return Math.round(m) + ' m';
    if (m < 10000) return (m / 1000).toFixed(1).replace('.', ',') + ' km';
    return Math.round(m / 1000) + ' km';
  }

  function toast(msg, off) {
    var el = document.createElement('div');
    el.className = 'toast' + (off ? ' toast-off' : '');
    el.textContent = msg;
    elToasts.appendChild(el);
    setTimeout(function () { el.remove(); }, 4200);
    while (elToasts.children.length > 4) elToasts.firstChild.remove();
  }

  // ---------- Carte ----------
  function initMap() {
    map = L.map('map', {
      center: [46.6, 2.4], // France par défaut
      zoom: 6,
      zoomControl: false,
      attributionControl: true,
      worldCopyJump: true
    });
    tiles = L.tileLayer('https://{s}.basemaps.cartocdn.com/dark_all/{z}/{x}/{y}{r}.png', {
      attribution: '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> &copy; <a href="https://carto.com/attributions">CARTO</a>',
      subdomains: 'abcd',
      maxZoom: 19
    });
    tiles.addTo(map);
    map.on('dragstart', userMovedMap);
    map.on('zoomstart', function () { if (!suppressMoveEvents) userMovedMap(); });
  }

  function userMovedMap() { follow = false; }

  function panTo(latlng, zoom) {
    suppressMoveEvents = true;
    map.setView(latlng, zoom || Math.max(map.getZoom(), 15), { animate: true });
    setTimeout(function () { suppressMoveEvents = false; }, 900);
  }

  // ---------- Rendu des présents ----------
  function markerHtml(p, isMe, stale) {
    var color = colorFor(p.hue || 0);
    return '<div class="blip-inner' + (stale ? ' blip-stale' : '') + '" style="--c:' + color + '">' +
      '<div class="blip-pulse"></div>' +
      '<div class="blip-dot"></div>' +
      '<div class="blip-label">' + escapeHtml(p.name || '?') + (isMe ? ' (moi)' : '') + '</div>' +
      '</div>';
  }

  // Coalescence : les snapshots RTDB peuvent arriver en rafale
  function repaint() {
    if (repaintQueued) return;
    repaintQueued = true;
    var wait = Math.max(0, 250 - (Date.now() - lastRepaintAt));
    setTimeout(function () {
      repaintQueued = false;
      lastRepaintAt = Date.now();
      doRepaint();
    }, wait);
  }

  function doRepaint() {
    var now = serverNow();
    var uids = Object.keys(people);
    var liveCount = 0;

    uids.forEach(function (uid) {
      var p = people[uid];
      if (!p || typeof p.lat !== 'number' || typeof p.lng !== 'number') return;
      var age = now - (p.t || 0);

      // Nettoyage des zombies (crash sans onDisconnect) — une tentative max
      if (age > ZOMBIE_MS && uid !== myUid) {
        if (joined && !cleanedUids[uid]) {
          cleanedUids[uid] = true;
          db.ref('presence/' + uid).remove().catch(function () {});
        }
        removeMarker(uid);
        return;
      }

      var stale = age > STALE_MS;
      if (!stale) liveCount++;
      var isMe = uid === myUid;
      var sig = [p.name, p.hue, stale, isMe].join('|');
      var entry = markers[uid];

      if (!entry) {
        var icon = L.divIcon({ className: 'blip', html: markerHtml(p, isMe, stale), iconSize: [0, 0] });
        var m = L.marker([p.lat, p.lng], { icon: icon, keyboard: false, zIndexOffset: isMe ? 1000 : 0 });
        m.on('click', function () { panTo([people[uid].lat, people[uid].lng]); });
        m.addTo(map);
        markers[uid] = { marker: m, sig: sig };
      } else {
        entry.marker.setLatLng([p.lat, p.lng]);
        if (entry.sig !== sig) {
          entry.marker.setIcon(L.divIcon({ className: 'blip', html: markerHtml(p, isMe, stale), iconSize: [0, 0] }));
          entry.sig = sig;
        }
      }
    });

    // Marqueurs orphelins
    Object.keys(markers).forEach(function (uid) {
      if (!people[uid]) removeMarker(uid);
    });

    // Cercle de précision (moi)
    if (joined && lastPayload) {
      var acc = Math.min(lastPayload.acc || 0, 2000);
      if (acc > 15) {
        if (!accCircle) {
          accCircle = L.circle([lastPayload.lat, lastPayload.lng], {
            radius: acc, color: '#4af68a', weight: 1, opacity: 0.35,
            fillColor: '#4af68a', fillOpacity: 0.07, interactive: false
          }).addTo(map);
        } else {
          accCircle.setLatLng([lastPayload.lat, lastPayload.lng]);
          accCircle.setRadius(acc);
        }
      } else if (accCircle) {
        accCircle.remove();
        accCircle = null;
      }
    }

    renderCounts(liveCount);
    renderRoster(now);
  }

  function removeMarker(uid) {
    if (markers[uid]) {
      markers[uid].marker.remove();
      delete markers[uid];
    }
  }

  function renderCounts(liveCount) {
    // HUD
    elHudCount.textContent = liveCount + ' en ligne';
    // Écran d'accueil (on ne se compte pas soi-même : pas encore rejoint)
    if (!gotFirstSnapshot) return; // ne pas écraser « Radar injoignable »
    var others = liveCount;
    var txt;
    if (others <= 0) txt = 'Personne sur le radar pour l’instant — sois le premier.';
    else if (others === 1) txt = '1 personne est déjà sur le radar.';
    else txt = others + ' personnes sont déjà sur le radar.';
    elGateCount.textContent = txt;
  }

  function renderRoster(now) {
    if (!joined) return;
    var me = lastPayload;
    var rows = Object.keys(people)
      .filter(function (uid) {
        var p = people[uid];
        return p && typeof p.lat === 'number' && (now - (p.t || 0)) <= ZOMBIE_MS;
      })
      .map(function (uid) {
        var p = people[uid];
        var dist = (me && uid !== myUid) ? haversine(me.lat, me.lng, p.lat, p.lng) : -1;
        return { uid: uid, p: p, dist: dist, isMe: uid === myUid, stale: (now - (p.t || 0)) > STALE_MS };
      })
      .sort(function (a, b) {
        if (a.isMe) return -1;
        if (b.isMe) return 1;
        return a.dist - b.dist;
      });

    var sig = rows.map(function (r) {
      return [r.uid, r.p.name, r.p.hue, formatDist(r.dist), r.stale, r.isMe].join('|');
    }).join(';');
    if (sig === rosterSig) return;
    rosterSig = sig;

    elRoster.innerHTML = '';
    rows.forEach(function (r) {
      var chip = document.createElement('button');
      chip.className = 'chip' + (r.isMe ? ' chip-me' : '');
      chip.type = 'button';
      chip.setAttribute('aria-label', (r.p.name || '?') + (r.isMe ? ', moi' : ', à ' + formatDist(r.dist)));
      if (r.stale) chip.style.opacity = '0.45';

      var dot = document.createElement('span');
      dot.className = 'chip-dot';
      dot.style.setProperty('--c', colorFor(r.p.hue || 0));

      var name = document.createElement('span');
      name.className = 'chip-name';
      name.textContent = r.p.name || '?';

      var dist = document.createElement('span');
      dist.className = 'chip-dist';
      dist.textContent = r.isMe ? 'moi' : formatDist(r.dist);

      chip.appendChild(dot);
      chip.appendChild(name);
      chip.appendChild(dist);
      chip.addEventListener('click', function () { panTo([r.p.lat, r.p.lng]); });
      elRoster.appendChild(chip);
    });
  }

  // ---------- Toasts arrivée / départ ----------
  function diffPresence(newPeople) {
    var newUids = {};
    Object.keys(newPeople).forEach(function (uid) { newUids[uid] = true; });
    if (knownUids !== null) {
      Object.keys(newUids).forEach(function (uid) {
        if (!knownUids[uid] && uid !== myUid) {
          var p = newPeople[uid];
          if (p && p.name && serverNow() - (p.t || 0) < STALE_MS) {
            toast('📡 ' + p.name + ' apparaît sur le radar');
          }
        }
      });
      Object.keys(knownUids).forEach(function (uid) {
        if (!newUids[uid] && uid !== myUid) {
          var old = people[uid];
          // Pas de toast pour un nœud zombie nettoyé 10 min plus tard
          if (old && old.name && !cleanedUids[uid] && serverNow() - (old.t || 0) < STALE_MS * 2) {
            toast(old.name + ' a quitté le radar', true);
          }
        }
      });
    }
    knownUids = newUids;
  }

  // ---------- Firebase ----------
  function initFirebase() {
    firebase.initializeApp(window.RADAR_CONFIG);
    db = firebase.database();

    db.ref('.info/serverTimeOffset').on('value', function (snap) {
      serverOffset = snap.val() || 0;
    });

    // Lecture publique : la carte s'anime dès l'accueil
    db.ref('presence').on('value', function (snap) {
      gotFirstSnapshot = true;
      var val = snap.val() || {};
      diffPresence(val);
      people = val;
      repaint();
    }, function (err) {
      console.error('[radar] lecture presence:', err);
      elGateCount.textContent = 'Radar injoignable — réessaie plus tard.';
    });

    // Si rien ne répond, ne pas rester bloqué sur « Connexion au radar… »
    setTimeout(function () {
      if (!gotFirstSnapshot) {
        elGateCount.textContent = 'Radar injoignable — vérifie ta connexion.';
      }
    }, 8000);

    // Ré-armer la présence après une coupure réseau
    db.ref('.info/connected').on('value', function (snap) {
      if (snap.val() === true && joined && meRef && lastPayload) {
        meRef.onDisconnect().remove();
        var refresh = Object.assign({}, lastPayload, { t: firebase.database.ServerValue.TIMESTAMP });
        meRef.set(refresh).catch(function () {});
        lastPayload.t = serverNow();
      }
    });
  }

  function ensureAuth() {
    var auth = firebase.auth();
    if (auth.currentUser) return Promise.resolve(auth.currentUser);
    return auth.signInAnonymously().then(function (cred) { return cred.user; });
  }

  // ---------- Partage de position ----------
  function payloadFrom(fix, name, hue) {
    return {
      name: name,
      lat: Math.round(fix.coords.latitude * 1e6) / 1e6,
      lng: Math.round(fix.coords.longitude * 1e6) / 1e6,
      acc: Math.round(fix.coords.accuracy || 0),
      hue: hue,
      t: firebase.database.ServerValue.TIMESTAMP
    };
  }

  function writeFix(fix, force) {
    if (!joined || !meRef) return;
    var nowMs = Date.now();
    var moved = lastPayload
      ? haversine(lastPayload.lat, lastPayload.lng, fix.coords.latitude, fix.coords.longitude)
      : Infinity;
    if (!force && (nowMs - lastWriteAt < WRITE_MIN_MS || moved < WRITE_MIN_METERS)) return;

    var name = lastPayload ? lastPayload.name : cleanName(elCallsign.value) || randomCallsign();
    var hue = lastPayload ? lastPayload.hue : hueFromUid(myUid);
    var payload = payloadFrom(fix, name, hue);
    lastWriteAt = nowMs;
    lastPayload = Object.assign({}, payload, { t: serverNow() }); // copie locale avec t numérique
    meRef.set(payload).catch(function (err) {
      console.error('[radar] écriture presence:', err);
    });

    if (follow) panTo([payload.lat, payload.lng], Math.max(map.getZoom(), 15));
    repaint();
  }

  function geoErrorMessage(err) {
    if (!err) return 'Erreur de géolocalisation inconnue.';
    switch (err.code) {
      case 1: return 'Géolocalisation refusée. Autorise la position pour ce site dans ton navigateur, puis réessaie.';
      case 2: return 'Position indisponible. Vérifie que le GPS / la localisation est activé sur ton appareil.';
      case 3: return 'La localisation met trop de temps. Réessaie, si possible près d’une fenêtre.';
      default: return 'Erreur de géolocalisation (' + err.message + ').';
    }
  }

  function showGateError(msg) {
    elGateError.textContent = msg;
    elGateError.classList.remove('hidden');
  }

  // ---------- Rejoindre / quitter ----------
  function join() {
    if (joined || joining) return;
    elGateError.classList.add('hidden');

    if (!('geolocation' in navigator)) {
      showGateError('Ton navigateur ne permet pas la géolocalisation.');
      return;
    }
    if (!window.isSecureContext) {
      showGateError('La géolocalisation exige une page en HTTPS.');
      return;
    }

    var name = cleanName(elCallsign.value);
    if (!name) {
      name = randomCallsign();
      elCallsign.value = name;
    }
    try { localStorage.setItem('radar_name', name); } catch (e) {}

    joining = true;
    elJoin.disabled = true;
    elJoin.textContent = 'Acquisition du signal…';

    ensureAuth().then(function (user) {
      myUid = user.uid;
      meRef = db.ref('presence/' + myUid);

      if (watchId !== null) navigator.geolocation.clearWatch(watchId);
      watchId = navigator.geolocation.watchPosition(
        function (fix) {
          lastFix = fix;
          if (joining && !joined) {
            // Premier fix : on apparaît
            joining = false;
            joined = true;
            meRef.onDisconnect().remove();
            writeFix(fix, true);
            enterMapMode();
          } else if (joined) {
            writeFix(fix, false);
          }
        },
        function (err) {
          if (!joined) {
            if (watchId !== null) navigator.geolocation.clearWatch(watchId);
            watchId = null;
            joining = false;
            elJoin.disabled = false;
            elJoin.textContent = 'Apparaître sur le radar';
            showGateError(geoErrorMessage(err));
          } else {
            console.warn('[radar] geoloc:', err.message);
          }
        },
        { enableHighAccuracy: true, maximumAge: 5000, timeout: 20000 }
      );
    }).catch(function (err) {
      console.error('[radar] auth:', err);
      joining = false;
      elJoin.disabled = false;
      elJoin.textContent = 'Apparaître sur le radar';
      showGateError('Connexion au radar impossible (' + (err.code || err.message) + '). Réessaie.');
    });
  }

  function enterMapMode() {
    document.body.classList.remove('gated');
    elGate.classList.add('hidden');
    elHud.classList.remove('hidden');
    elRoster.classList.remove('hidden');
    elJoin.disabled = false;
    elJoin.textContent = 'Apparaître sur le radar';

    // Cadrage initial : tout le monde à l'écran si d'autres sont là
    var pts = [];
    var now = serverNow();
    Object.keys(people).forEach(function (uid) {
      var p = people[uid];
      if (p && typeof p.lat === 'number' && now - (p.t || 0) < STALE_MS) pts.push([p.lat, p.lng]);
    });
    if (lastPayload) pts.push([lastPayload.lat, lastPayload.lng]);
    suppressMoveEvents = true;
    if (pts.length > 1) {
      map.fitBounds(L.latLngBounds(pts).pad(0.25), { maxZoom: 15 });
      follow = false;
    } else if (lastPayload) {
      map.setView([lastPayload.lat, lastPayload.lng], 15);
      follow = true;
    }
    setTimeout(function () { suppressMoveEvents = false; }, 900);

    heartbeatTimer = setInterval(function () {
      if (joined && meRef && lastPayload) {
        var refresh = Object.assign({}, lastPayload, { t: firebase.database.ServerValue.TIMESTAMP });
        meRef.set(refresh).catch(function () {});
        lastPayload.t = serverNow();
      }
    }, HEARTBEAT_MS);

    repaint();
  }

  function quit() {
    joined = false;
    joining = false;
    if (watchId !== null) {
      navigator.geolocation.clearWatch(watchId);
      watchId = null;
    }
    clearInterval(heartbeatTimer);
    if (meRef) {
      meRef.onDisconnect().cancel();
      meRef.remove().catch(function () {});
    }
    lastPayload = null;
    lastWriteAt = 0;
    if (accCircle) { accCircle.remove(); accCircle = null; }
    follow = true;
    document.body.classList.add('gated');
    elHud.classList.add('hidden');
    elRoster.classList.add('hidden');
    elGate.classList.remove('hidden');
    repaint();
  }

  function share() {
    var data = { title: 'Radar', text: 'Rejoins-moi sur le radar 📡', url: SHARE_URL };
    if (navigator.share) {
      navigator.share(data).catch(function () {});
    } else if (navigator.clipboard) {
      navigator.clipboard.writeText(SHARE_URL).then(function () {
        toast('Lien copié — envoie-le !');
      }).catch(function () {
        toast(SHARE_URL);
      });
    } else {
      toast(SHARE_URL);
    }
  }

  // ---------- Événements UI ----------
  elJoin.addEventListener('click', join);
  elReroll.addEventListener('click', function () {
    elCallsign.value = randomCallsign();
  });
  elCallsign.addEventListener('keydown', function (e) {
    if (e.key === 'Enter') join();
  });
  $('btn-quit').addEventListener('click', quit);
  $('btn-share').addEventListener('click', share);
  $('btn-center').addEventListener('click', function () {
    follow = true;
    if (lastPayload) panTo([lastPayload.lat, lastPayload.lng], Math.max(map.getZoom(), 15));
  });

  // Retour d'onglet : rafraîchir tout de suite la présence
  document.addEventListener('visibilitychange', function () {
    if (!document.hidden && joined && lastFix) writeFix(lastFix, true);
  });
  window.addEventListener('pagehide', function () {
    // onDisconnect s'en charge côté serveur ; on tente aussi localement
    if (joined && meRef) meRef.remove().catch(function () {});
  });

  // ---------- Démarrage ----------
  document.body.classList.add('gated');
  var savedName = null;
  try { savedName = localStorage.getItem('radar_name'); } catch (e) {}
  elCallsign.value = savedName || randomCallsign();

  initMap();
  initFirebase();
  repaintTimer = setInterval(repaint, 15000); // fraîcheur des états stale, même avant de rejoindre
})();
